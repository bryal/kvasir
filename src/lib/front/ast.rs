use lib::set_of;
use super::SrcPos;
use itertools::{zip, Itertools};
use std::collections::{BTreeMap, BTreeSet};
use std::{borrow, fmt, hash, mem, path};
use std::iter::once;

// TODO: Replace static with const to allow matching
lazy_static! {
    pub static ref TYPE_NIL: Type<'static> = Type::Const("Nil", None);
    pub static ref TYPE_BOOL: Type<'static> = Type::Const("Bool", None);
    pub static ref TYPE_FLOAT64: Type<'static> = Type::Const("Float64", None);
    pub static ref TYPE_STRING: Type<'static> = Type::Const("String", None);
    pub static ref TYPE_REALWORLD: Type<'static> = Type::Const("RealWorld", None);
}

/// A Polytype / Type scheme
///
/// Lika a lambda at type level. Where the parameter types of a lambda
/// limit what values may be passed as arguments, the parameter
/// constraints of a polytype similarly limit what types may be passed
/// as arguments.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poly<'s> {
    pub params: BTreeMap<TVar<'s>, BTreeSet<&'s str>>,
    pub body: Type<'s>,
}

impl<'s> Poly<'s> {
    fn is_monomorphic_in_context(&self, bound: &mut BTreeSet<TVar<'s>>) -> bool {
        self.params.is_empty() && self.body.is_monomorphic_in_context(bound)
    }

    pub fn is_monomorphic(&self) -> bool {
        self.is_monomorphic_in_context(&mut BTreeSet::new())
    }
}

impl<'s> fmt::Display for Poly<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let params_s = self.params
            .iter()
            .map(|(tv, cs)| {
                let cs_s = cs.iter()
                    .map(|c| c.to_string())
                    .intersperse(" ".to_string())
                    .collect::<String>();
                format!("({} {})", tv, cs_s)
            })
            .intersperse(" ".to_string())
            .collect::<String>();
        write!(f, "(for [{}] {})", params_s, self.body)
    }
}

/// A type function
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeFunc<'s> {
    Const(&'s str),
    Poly(Poly<'s>),
}

impl<'s> fmt::Display for TypeFunc<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeFunc::Const(s) => fmt::Display::fmt(s, f),
            TypeFunc::Poly(ref p) => fmt::Display::fmt(p, f),
        }
    }
}

/// A type variable. Either an explicit string name,
/// or an implicit automatically generated unique integer id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TVar<'s> {
    Explicit(&'s str),
    Implicit(u64),
}

impl<'s> fmt::Display for TVar<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TVar::Explicit(s) => write!(f, "{}", s),
            TVar::Implicit(n) => write!(f, "${}", n),
        }
    }
}

// TODO: This is weird. Probably wrong. Each type variable should not carry constraints?
//       optionally being explicit kind of makes sense though, but maybe explicit, locked
//       type variables should be a discinct variant?

/// A type
#[derive(Clone, Debug, PartialOrd, Ord, Hash)]
pub enum Type<'s> {
    /// A type variable uniquely identified by an integer id
    /// and constrained by a set of type classes
    Var(TVar<'s>),
    /// A monotype constant, like `int`, or `string`
    ///
    /// Can also refer to user-defined algebraic data types
    Const(&'s str, Option<SrcPos<'s>>),
    /// An application of a type function over one/some/no monotype(s)
    App(Box<TypeFunc<'s>>, Vec<Type<'s>>),
    /// A polytype
    Poly(Box<Poly<'s>>),
}

/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'s> Type<'s> {
    pub fn new_func(arg: Type<'s>, ret: Type<'s>) -> Self {
        Type::App(Box::new(TypeFunc::Const("->")), vec![arg, ret])
    }

    pub fn new_currying_func(args: &[Type<'s>], ret: Type<'s>) -> Self {
        args.iter()
            .rev()
            .cloned()
            .fold(ret, |acc, t| Type::new_func(t, acc))
    }

    pub fn new_io(ret: Type<'s>) -> Self {
        Type::new_func(
            TYPE_REALWORLD.clone(),
            Type::new_cons(ret, TYPE_REALWORLD.clone()),
        )
    }

    pub fn new_cons(car_typ: Type<'s>, cdr_typ: Type<'s>) -> Self {
        Type::App(Box::new(TypeFunc::Const("Cons")), vec![car_typ, cdr_typ])
    }

    pub fn new_tuple(types: &[Type<'s>]) -> Self {
        if let Some((last, init)) = types.split_last() {
            init.iter()
                .rev()
                .cloned()
                .fold(last.clone(), |acc, t| Type::new_cons(t, acc))
        } else {
            TYPE_NIL.clone()
        }
    }

    pub fn new_ptr(typ: Type<'s>) -> Self {
        Type::App(Box::new(TypeFunc::Const("Ptr")), vec![typ])
    }

    pub fn new_binop(typ: Type<'s>) -> Self {
        Type::new_func(Type::new_cons(typ.clone(), typ.clone()), typ)
    }

    pub fn new_relational_binop(typ: Type<'s>) -> Self {
        Type::new_func(Type::new_cons(typ.clone(), typ), Type::Const("Bool", None))
    }

    pub fn new_logic_binop() -> Self {
        Type::new_func(
            Type::new_cons(Type::Const("Bool", None), Type::Const("Bool", None)),
            Type::Const("Bool", None),
        )
    }

    /// If this type is an instantiated polytype, return the instantiation args
    pub fn get_inst_args(&self) -> Option<&[Type<'s>]> {
        match *self {
            Type::App(box TypeFunc::Poly(_), ref args) => Some(args),
            _ => None,
        }
    }

    fn is_monomorphic_in_context(&self, bound: &mut BTreeSet<TVar<'s>>) -> bool {
        match *self {
            Type::Var(ref v) => bound.contains(&v),
            Type::Const(_, _) => true,
            Type::App(ref f, ref args) => {
                let all_args_mono = args.iter().all(|arg| arg.is_monomorphic_in_context(bound));
                match **f {
                    TypeFunc::Const(_) => all_args_mono,
                    TypeFunc::Poly(ref p) => {
                        let mut dup = BTreeSet::new();
                        for (&tv, _) in &p.params {
                            if !bound.insert(tv) {
                                dup.insert(tv);
                            }
                        }
                        let body_is_mono = p.body.is_monomorphic_in_context(bound);
                        for tv in p.params
                            .iter()
                            .map(|(tv, _)| tv)
                            .filter(|tv| !dup.contains(tv))
                        {
                            bound.remove(tv);
                        }
                        all_args_mono && body_is_mono
                    }
                }
            }
            Type::Poly(ref p) => p.is_monomorphic_in_context(bound),
        }
    }

    /// Returns whether type is completly monomorphic
    pub fn is_monomorphic(&self) -> bool {
        self.is_monomorphic_in_context(&mut BTreeSet::new())
    }

    pub fn canonicalize_in_context(&self, s: &mut BTreeMap<TVar<'s>, Type<'s>>) -> Type<'s> {
        match *self {
            Type::Const(_, _) => self.clone(),
            Type::Var(ref tv) => s.get(tv).unwrap_or(self).clone(),
            Type::App(box TypeFunc::Const(c), ref args) => Type::App(
                Box::new(TypeFunc::Const(c)),
                args.iter()
                    .map(|arg| arg.canonicalize_in_context(s))
                    .collect(),
            ),
            Type::App(box TypeFunc::Poly(ref p), ref args) => {
                let shadoweds = zip(&p.params, args)
                    .filter_map(|((&param_v, _), arg)| {
                        s.insert(param_v, arg.clone()).map(|shad| (param_v, shad))
                    })
                    .collect::<Vec<_>>();
                let b = p.body.canonicalize_in_context(s);
                s.extend(shadoweds);
                b
            }
            Type::Poly(ref p) => Type::Poly(Box::new(Poly {
                params: p.params.clone(),
                body: p.body.canonicalize_in_context(s),
            })),
        }
    }

    /// Recursively apply applications to polytypes
    ///
    /// # Examples
    /// `canonicalize (app (poly (t u) (-> t u)) Int Float) == (-> Int Float)`
    pub fn canonicalize(&self) -> Type<'s> {
        self.canonicalize_in_context(&mut BTreeMap::new())
    }

    /// If a type constant, return the name
    pub fn get_const(&self) -> Option<&'s str> {
        match *self {
            Type::Const(s, _) => Some(s),
            _ => None,
        }
    }

    fn _int_size(s: &str, ptr_size: usize) -> Option<usize> {
        match s {
            "Int8" => Some(8),
            "Int16" => Some(16),
            "Int32" => Some(32),
            "Int64" => Some(64),
            "IntPtr" => Some(ptr_size),
            _ => None,
        }
    }

    /// If a signed integer, return int size
    pub fn int_size(&self, ptr_size: usize) -> Option<usize> {
        self.get_const().and_then(|s| Type::_int_size(s, ptr_size))
    }

    /// Returns whether the type is a signed integer
    pub fn is_int(&self) -> bool {
        self.int_size(0).is_some()
    }

    /// If an unsigned integer, return int size
    pub fn uint_size(&self, ptr_size: usize) -> Option<usize> {
        match *self {
            Type::Const(s, _) if s.starts_with('U') => Type::_int_size(&s[1..], ptr_size),
            _ => None,
        }
    }

    /// Returns whether the type is an unsigned integer
    pub fn is_uint(&self) -> bool {
        self.uint_size(0).is_some()
    }

    /// If a float, return size
    pub fn float_size(&self) -> Option<usize> {
        match *self {
            Type::Const("Float32", _) => Some(32),
            Type::Const("Float64", _) => Some(64),
            _ => None,
        }
    }

    /// Returns whether the type is a float
    pub fn is_float(&self) -> bool {
        self.float_size().is_some()
    }

    /// If a type variable with only the `Num` constraint, translate
    /// to default integer type Int64
    pub fn var_to_int64(&self) -> Self {
        match *self {
            Type::Var(_) => Type::Const("Int64", None),
            _ => self.clone(),
        }
    }

    fn get_bin(&self, con: &'s str) -> Option<(&Type<'s>, &Type<'s>)> {
        match *self {
            Type::App(ref f, ref ts) if **f == TypeFunc::Const(con) => {
                assert_eq!(ts.len(), 2);
                Some((&ts[0], &ts[1]))
            }
            _ => None,
        }
    }

    /// If the type is a function type signature, extract the parameter type and the return type.
    pub fn get_func(&self) -> Option<(&Type<'s>, &Type<'s>)> {
        self.get_bin("->")
    }

    /// If the type is of the form `(-> (Cons A B) C)`, return the tuple `(A, B, C)`
    pub fn get_cons_binary_func(&self) -> Option<(&Type<'s>, &Type<'s>, &Type<'s>)> {
        self.get_func()
            .and_then(|(c, r)| c.get_cons().map(|(a, b)| (a, b, r)))
    }

    /// If binop, by the definition of binops as : S x S -> S, return the operand type
    pub fn get_cons_binop(&self) -> Option<&Self> {
        if let Some((a, b, r)) = self.get_cons_binary_func() {
            if a == b && b == r {
                Some(a)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// If binary relational operation, by the definition : S x S -> Bool, return the operand type
    pub fn get_cons_relational_binop(&self) -> Option<&Self> {
        if let Some((a, b, r)) = self.get_cons_binary_func() {
            if a == b && r.get_const() == Some("Bool") {
                Some(a)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Returns whether type is binary logic operation: `and`, `or`, etc
    pub fn is_cons_logic_binop(&self) -> bool {
        if let Some((a, b, r)) = self.get_cons_binary_func() {
            a == b && b == r && r.get_const() == Some("Bool")
        } else {
            false
        }
    }

    pub fn get_cons(&self) -> Option<(&Type<'s>, &Type<'s>)> {
        self.get_bin("Cons")
    }

    pub fn fulfills_constraints(&self, cs: &BTreeSet<&str>) -> bool {
        use self::Type::*;
        cs.iter().all(|c| match *c {
            "Num" => match *self {
                Const("Int8", _)
                | Const("Int16", _)
                | Const("Int32", _)
                | Const("Int64", _)
                | Const("IntPtr", _)
                | Const("UInt8", _)
                | Const("UInt16", _)
                | Const("UInt32", _)
                | Const("UInt64", _)
                | Const("UIntPtr", _)
                | Const("Bool", _)
                | Const("Float32", _)
                | Const("Float64", _) => true,
                _ => false,
            },
            _ => unimplemented!(),
        })
    }
}

impl<'s> PartialEq for Type<'s> {
    fn eq(&self, other: &Self) -> bool {
        use self::Type::*;
        match (self, other) {
            (&Var(ref v1), &Var(ref v2)) => v1 == v2,
            (&Const(t, _), &Const(u, _)) => t == u,
            (&App(ref f, ref v), &App(ref g, ref w)) => f == g && v == w,
            (&Poly(ref p), &Poly(ref q)) => p == q,
            _ => false,
        }
    }
}

impl<'s> Eq for Type<'s> {}

impl<'s> fmt::Display for Type<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Var(ref tv) => tv.fmt(f),
            Type::Const(s, _) => fmt::Display::fmt(s, f),
            Type::App(ref con, ref args) => {
                let args_s = args.iter()
                    .map(ToString::to_string)
                    .intersperse(" ".to_string())
                    .collect::<String>();
                write!(f, "({} {})", con, args_s)
            }
            Type::Poly(ref p) => fmt::Display::fmt(p, f),
        }
    }
}

/// An identifier
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ident<'s> {
    pub s: &'s str,
    pub pos: SrcPos<'s>,
}
impl<'s> Ident<'s> {
    pub fn new(s: &'s str, pos: SrcPos<'s>) -> Ident<'s> {
        Ident { s: s, pos: pos }
    }
}
impl<'s> PartialEq<str> for Ident<'s> {
    fn eq(&self, rhs: &str) -> bool {
        self.s == rhs
    }
}
impl<'s> hash::Hash for Ident<'s> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.s.hash(state);
    }
}
impl<'s> borrow::Borrow<str> for Ident<'s> {
    fn borrow(&self) -> &str {
        &self.s
    }
}
impl<'s> fmt::Display for Ident<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.s, f)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ExternDecl<'s> {
    pub ident: Ident<'s>,
    /// The type of the external variable being declared.
    ///
    /// Guaranteed during parsing to be monomorphic and canonical
    /// I.e. no type variables or polytype applications
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Nil<'s> {
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct NumLit<'s> {
    pub lit: &'s str,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct StrLit<'s> {
    pub lit: borrow::Cow<'s, str>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Variable<'s> {
    pub ident: Ident<'s>,
    pub typ: Type<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Bool<'s> {
    pub val: bool,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct App<'s> {
    pub func: Expr<'s>,
    pub arg: Expr<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

/// if-then-else expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct If<'s> {
    pub predicate: Expr<'s>,
    pub consequent: Expr<'s>,
    pub alternative: Expr<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Lambda<'s> {
    pub param_ident: Ident<'s>,
    pub param_type: Type<'s>,
    pub body: Expr<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

/// A binding of a name to a value, i.e. a variable definition.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Binding<'s> {
    pub ident: Ident<'s>,
    pub sig: Poly<'s>,
    pub val: Expr<'s>,
    /// If this binding is polymorphic, here will be mappings from
    /// application arguments to monomorphic instantiation of `val`
    pub mono_insts: BTreeMap<Vec<Type<'s>>, Expr<'s>>,
    pub pos: SrcPos<'s>,
}

impl<'s> Binding<'s> {
    pub fn get_type(&self) -> Type<'s> {
        if self.sig.params.is_empty() {
            self.sig.body.clone()
        } else {
            Type::Poly(box self.sig.clone())
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Group<'s> {
    Circular(BTreeMap<&'s str, Binding<'s>>),
    Uncircular(&'s str, Binding<'s>),
}

impl<'s> Group<'s> {
    pub fn contains(&self, e: &str) -> bool {
        match *self {
            Group::Circular(ref xs) => xs.contains_key(e),
            Group::Uncircular(x, _) => e == x,
        }
    }

    pub fn ids<'a>(&'a self) -> Box<Iterator<Item = &'s str> + 'a> {
        match *self {
            Group::Circular(ref xs) => Box::new(xs.keys().map(|s| *s)),
            Group::Uncircular(x, _) => Box::new(once(x)),
        }
    }

    pub fn bindings<'g>(&'g self) -> Box<Iterator<Item = &'g Binding<'s>> + 'g> {
        match *self {
            Group::Circular(ref xs) => Box::new(xs.iter().map(|(_, b)| b)),
            Group::Uncircular(_, ref b) => Box::new(once(b)),
        }
    }

    pub fn bindings_mut<'g>(&'g mut self) -> Box<Iterator<Item = &'g mut Binding<'s>> + 'g> {
        match *self {
            Group::Circular(ref mut xs) => Box::new(xs.iter_mut().map(|(_, b)| b)),
            Group::Uncircular(_, ref mut b) => Box::new(once(b)),
        }
    }
}

/// A representation of let-bindings that describes the dependencies of the bindings to each other
///
/// In a set of simultaneously defined bindings (i.e. the bindings of a let-form), bindings may
/// be defined in terms of each other. These relationships can be represented with a disjoint
/// union of directed, acyclic graphs where a node is a cyclic graph of recursively defined
/// bindings.
///
/// As the graphs are DAGs, the groups can be ordered topologically. Type inference is now simple.
/// We start at the end of the topological order and infer types group-wise in reverse order.
///
/// Within a cyclical group, we begin inference in an arbitrary definition. If a variable referring
/// to a binding within the group is encountered, recursively infer in the definition of that
/// variable and record the jump. If a variable referring to a binding is encountered that is
/// already in the jump stack, no more information can be gained from following the variable, so
/// just get the current type of the variable. When done inferring in a definition, do not
/// generalize the type. Only when the whole group has been inferred, generalize the types of the
/// definitions as a group. I.e., all bindings will have take the same type arguments.
///
/// # Example
///
/// The following definitions together constitute a single DAG
///
/// ```lisp
/// (define (id x)       ; Will be in a group on its own as no recursive definition in terms of
///   x)                 ; anything else. The group it constitutes is a leaf node in it's
///                      ; super-graph as it does not refer to anything n the same scope even
///                      ; non-recursively.
///
/// (define (id2 x)      ; No recursion, group on its own. Refers to `id` in same scope, so not a
///   (id x))            ; leaf group => higher in the topological order than group of `id`
///
/// (define (f n x)      ; `f` refers to `g` which refers to `f` and so on. They are mutually
///   (if (= n 0)        ; recursive, and as such, together they constitute a group. `g` further
///       x              ; refers to `id2` of the same scope, which implies that this group
///     (g (- n 1) x)))  ; is higher in the topoligical order than id2.
///
/// (define (g n x)
///   (id2 (f n x)))
/// ```
///
/// To infer types, we no start at the bottom of the topological order. `id` does not refer to
/// anything in the same scope, and is easily inferred to be of type `(for (t) (-> t t))`.
///
/// We move a step up in the order and get the group of `id2`. In `id2`, we simply instantiate
/// `id`s type of `(for (t) (-> t t))` with fresh type variables, and we get `(:: id (u))`
/// which implies `(: id (-> u u))`. `id2` is then generalized to `(for (u) (-> u u))`.
///
/// For the topmost group of `f` and `g`, we begin inference in `f`. We infer that the type of
/// `n` is `Int`, and that the type of the second argument, `x`, is the same as the return type.
/// Then we dive into `g`. Here we unify the parameter types of `(: f (-> Int a a))` with the types
/// of `g`s parameters `n` and `x`, and together with the return type of `f` and an instantiation
/// of `id2`, we get `(: g (-> Int a a))`. Finally, we return to `f` and then return from inference.
/// Now that all bindings in group has been inferred, we generalize. The only free type variable is
/// `a`. Both `f` and `g` are given the same type parameters, and the result is
/// `(: f (for (a) (-> Int a a)))` and `(: g (for (a) (-> Int a a)))`.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TopologicallyOrderedDependencyGroups<'s>(pub Vec<Group<'s>>);

impl<'s> TopologicallyOrderedDependencyGroups<'s> {
    pub fn ids<'a>(&'a self) -> Box<Iterator<Item = &'s str> + 'a> {
        Box::new(self.groups().flat_map(|g| g.ids()))
    }

    /// Returns an iterator of bindings from the root of the topological order
    pub fn bindings<'g>(&'g self) -> Box<DoubleEndedIterator<Item = &'g Binding<'s>> + 'g> {
        Box::new(
            self.groups()
                .flat_map(|g| g.bindings())
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    /// Returns an iterator bindings from the root of the topological order
    pub fn bindings_mut<'g>(
        &'g mut self,
    ) -> Box<DoubleEndedIterator<Item = &'g mut Binding<'s>> + 'g> {
        Box::new(
            self.groups_mut()
                .flat_map(|g| g.bindings_mut())
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    /// Returns an iterator of groups from the root of the topological order
    pub fn groups<'g>(&'g self) -> Box<DoubleEndedIterator<Item = &'g Group<'s>> + 'g> {
        Box::new(self.0.iter())
    }

    /// Returns an iterator of groups from the root of the topological order
    pub fn groups_mut<'g>(&'g mut self) -> Box<DoubleEndedIterator<Item = &'g mut Group<'s>> + 'g> {
        Box::new(self.0.iter_mut())
    }
}

/// A `let` special form
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Let<'s> {
    pub bindings: TopologicallyOrderedDependencyGroups<'s>,
    pub body: Expr<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

/// A type ascription.
///
/// Ascribes a specific type to an expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeAscript<'s> {
    pub typ: Type<'s>,
    pub expr: Expr<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Cons<'s> {
    pub typ: Type<'s>,
    pub car: Expr<'s>,
    pub cdr: Expr<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Car<'s> {
    pub typ: Type<'s>,
    pub expr: Expr<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Cdr<'s> {
    pub typ: Type<'s>,
    pub expr: Expr<'s>,
    pub pos: SrcPos<'s>,
}

/// A type cast
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Cast<'s> {
    pub expr: Expr<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct OfVariant<'s> {
    pub expr: Expr<'s>,
    pub variant: Ident<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct AsVariant<'s> {
    pub expr: Expr<'s>,
    pub variant: Ident<'s>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct New<'s> {
    pub constr: Ident<'s>,
    pub members: Vec<Expr<'s>>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Deconstr<'s> {
    pub constr: Ident<'s>,
    pub subpatts: Vec<Pattern<'s>>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Pattern<'s> {
    Nil(Nil<'s>),
    NumLit(NumLit<'s>),
    StrLit(StrLit<'s>),
    Variable(Variable<'s>),
    Deconstr(Box<Deconstr<'s>>),
}

impl<'s> Pattern<'s> {
    pub fn variables(&self) -> BTreeSet<&Variable<'s>> {
        match *self {
            Pattern::Variable(ref v) => set_of(v),
            Pattern::Deconstr(ref d) => d.subpatts.iter().flat_map(|p| p.variables()).collect(),
            _ => BTreeSet::new(),
        }
    }

    pub fn variables_mut(&mut self) -> BTreeSet<&mut Variable<'s>> {
        match *self {
            Pattern::Variable(ref mut v) => set_of(v),
            Pattern::Deconstr(ref mut d) => d.subpatts
                .iter_mut()
                .flat_map(|p| p.variables_mut())
                .collect(),
            _ => BTreeSet::new(),
        }
    }

    pub fn variable_names(&self) -> BTreeSet<&'s str> {
        match *self {
            Pattern::Variable(ref v) => set_of(v.ident.s),
            Pattern::Deconstr(ref d) => {
                d.subpatts.iter().flat_map(|p| p.variable_names()).collect()
            }
            _ => BTreeSet::new(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Case<'s> {
    pub patt: Pattern<'s>,
    pub patt_typ: Type<'s>,
    pub body: Expr<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Match<'s> {
    pub expr: Expr<'s>,
    pub cases: Vec<Case<'s>>,
    pub typ: Type<'s>,
    pub pos: SrcPos<'s>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr<'s> {
    Nil(Nil<'s>),
    NumLit(NumLit<'s>),
    StrLit(StrLit<'s>),
    Bool(Bool<'s>),
    Variable(Variable<'s>),
    App(Box<App<'s>>),
    If(Box<If<'s>>),
    Lambda(Box<Lambda<'s>>),
    Let(Box<Let<'s>>),
    TypeAscript(Box<TypeAscript<'s>>),
    Cons(Box<Cons<'s>>),
    Car(Box<Car<'s>>),
    Cdr(Box<Cdr<'s>>),
    Cast(Box<Cast<'s>>),
    OfVariant(Box<OfVariant<'s>>),
    AsVariant(Box<AsVariant<'s>>),
    New(Box<New<'s>>),
    Match(Box<Match<'s>>),
}

impl<'s> Expr<'s> {
    pub fn pos(&self) -> &SrcPos<'s> {
        match *self {
            Expr::Nil(ref n) => &n.pos,
            Expr::NumLit(ref l) => &l.pos,
            Expr::StrLit(ref l) => &l.pos,
            Expr::Bool(ref b) => &b.pos,
            Expr::Variable(ref bnd) => &bnd.ident.pos,
            Expr::App(ref app) => &app.pos,
            Expr::If(ref cond) => &cond.pos,
            Expr::Lambda(ref l) => &l.pos,
            Expr::Let(ref l) => &l.pos,
            Expr::TypeAscript(ref a) => &a.pos,
            Expr::Cons(ref c) => &c.pos,
            Expr::Car(ref c) => &c.pos,
            Expr::Cdr(ref c) => &c.pos,
            Expr::Cast(ref c) => &c.pos,
            Expr::OfVariant(ref x) => &x.pos,
            Expr::AsVariant(ref x) => &x.pos,
            Expr::New(ref n) => &n.pos,
            Expr::Match(ref m) => &m.pos,
        }
    }

    pub fn as_var(&self) -> Option<&Variable<'s>> {
        match *self {
            Expr::Variable(ref bnd) => Some(bnd),
            _ => None,
        }
    }

    pub fn get_type(&self) -> &Type<'s> {
        match *self {
            Expr::Nil(_) => &TYPE_NIL,
            Expr::NumLit(ref l) => &l.typ,
            Expr::StrLit(_) => &TYPE_STRING,
            Expr::Bool(_) => &TYPE_BOOL,
            Expr::Variable(ref bnd) => &bnd.typ,
            Expr::App(ref app) => &app.typ,
            Expr::If(ref cond) => &cond.typ,
            Expr::Lambda(ref l) => &l.typ,
            Expr::Let(ref l) => &l.typ,
            Expr::TypeAscript(ref a) => &a.typ,
            Expr::Cons(ref c) => &c.typ,
            Expr::Car(ref c) => &c.typ,
            Expr::Cdr(ref c) => &c.typ,
            Expr::Cast(ref c) => &c.typ,
            Expr::OfVariant(_) => &TYPE_BOOL,
            Expr::AsVariant(ref x) => &x.typ,
            Expr::New(ref n) => &n.typ,
            Expr::Match(ref m) => &m.typ,
        }
    }

    pub fn first_non_type_ascr_is_lambda(&self) -> bool {
        match *self {
            Expr::Lambda(_) => true,
            Expr::TypeAscript(ref a) => a.expr.first_non_type_ascr_is_lambda(),
            _ => false,
        }
    }

    /// If `expr` refers to a type ascription, remove the ascription,
    /// point `expr` to the inner, ascribed expression,
    /// and return the ascribed type
    ///
    /// Returns `None` if `expr` is not a type ascription
    pub fn remove_type_ascription(&mut self) -> Option<Type<'s>> {
        let (t, inner) = if let Expr::TypeAscript(ref mut ascr) = *self {
            // use dummy pos and replace with `Nil` to avoid unsafe.
            // Will be deallocated immediately afterwards
            let dummy_pos = super::SrcPos::new_pos(path::Path::new(""), "", 0);
            let inner = mem::replace(&mut ascr.expr, Expr::Nil(Nil { pos: dummy_pos }));
            (ascr.typ.clone(), inner)
        } else {
            return None;
        };
        *self = inner;
        Some(t)
    }
}

/// A variant of an algebraic data type
///
/// An ADT variant is equivalent to a constructor and a destructor
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct AdtVariant<'s> {
    pub name: Ident<'s>,
    pub members: Vec<Type<'s>>,
    pub pos: SrcPos<'s>,
}

impl<'s> AdtVariant<'s> {
    pub fn get_type(&self) -> Type<'s> {
        Type::new_tuple(&self.members)
    }
}

/// Algebraic Data Type definition
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct AdtDef<'s> {
    pub name: Ident<'s>,
    pub variants: Vec<AdtVariant<'s>>,
    pub pos: SrcPos<'s>,
}

impl<'s> AdtDef<'s> {
    pub fn get_type(&self) -> Type<'s> {
        Type::Const(self.name.s, None)
    }

    pub fn variant_index(&self, v: &str) -> Option<usize> {
        self.variants.iter().position(|av| av.name.s == v)
    }
}

/// Algebraic data type definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Adts<'s> {
    pub defs: BTreeMap<&'s str, AdtDef<'s>>,
    /// Auxiliary map for quicker access to variants parent
    pub variants: BTreeMap<&'s str, &'s str>,
}

impl<'s> Adts<'s> {
    pub fn new() -> Self {
        Adts {
            defs: BTreeMap::new(),
            variants: BTreeMap::new(),
        }
    }

    fn is_rec_const(&self, name: &str, origin: &str) -> bool {
        if name == origin {
            true
        } else if let Some(def) = self.defs.get(name) {
            self.is_rec_adt(def, origin)
        } else {
            false
        }
    }

    fn is_rec_typefunc(&self, tf: &TypeFunc, origin: &str) -> bool {
        match *tf {
            TypeFunc::Const(s) => self.is_rec_const(s, origin),
            TypeFunc::Poly(ref p) => self.is_rec_type(&p.body, origin),
        }
    }

    fn is_rec_type(&self, t: &Type, origin: &str) -> bool {
        match *t {
            Type::Const(s, _) => self.is_rec_const(s, origin),
            Type::App(ref tf, ref targs) => {
                self.is_rec_typefunc(tf, origin)
                    || targs.iter().any(|t| self.is_rec_type(t, origin))
            }
            Type::Poly(ref p) => self.is_rec_type(&p.body, origin),
            _ => false,
        }
    }

    fn is_rec_adt(&self, adt: &AdtDef, origin: &str) -> bool {
        adt.variants
            .iter()
            .any(|v| v.members.iter().any(|t| self.is_rec_type(t, origin)))
    }

    pub fn variant_is_recursive(&self, v: &str) -> bool {
        let adt_name = self.parent_adt_of_variant(v)
            .expect("ICE: No parent_adt_of_variant in adt_variant_is_recursive")
            .name
            .s;
        let typ = self.parent_type_of_variant(v)
            .expect("ICE: No parent_type_of_variant in adt_variant_is_recursive");
        self.is_rec_type(&typ, adt_name)
    }

    pub fn adt_is_recursive(&self, adt: &AdtDef) -> bool {
        self.is_rec_adt(adt, adt.name.s)
    }

    pub fn adt_of_variant_is_recursive(&self, v: &str) -> bool {
        let adt = self.parent_adt_of_variant(v)
            .expect("ICE: No parent adt of variant in adt_of_variant_is_recursive");
        self.adt_is_recursive(adt)
    }

    pub fn parent_adt_of_variant<'a>(&'a self, v: &str) -> Option<&'a AdtDef<'s>> {
        self.variants.get(v).and_then(|t| self.defs.get(t))
    }

    pub fn parent_type_of_variant<'a>(&'a self, v: &str) -> Option<Type<'s>> {
        self.variants.get(v).map(|t| Type::Const(t, None))
    }

    pub fn adt_variant_of_name<'a>(&'a self, v: &str) -> Option<&'a AdtVariant<'s>> {
        self.parent_adt_of_variant(v)
            .and_then(|parent_adt| parent_adt.variants.iter().find(|av| av.name.s == v))
    }

    pub fn type_of_variant(&self, v: &str) -> Option<Type<'s>> {
        self.adt_variant_of_name(v).map(AdtVariant::get_type)
    }

    pub fn constructor_type_of_variant(&self, v: &str) -> Option<Type<'s>> {
        let adt_variant = self.adt_variant_of_name(v)?;
        let parent_type = self.parent_type_of_variant(v)?;
        Some(Type::new_currying_func(&adt_variant.members, parent_type))
    }

    pub fn variant_index(&self, v: &str) -> Option<usize> {
        self.parent_adt_of_variant(v)?.variant_index(v)
    }

    pub fn variant_exists(&self, v: &str) -> bool {
        self.variants.contains_key(v)
    }
}

/// A module of definitions and declarations of functions and variables
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Ast<'s> {
    /// External variable declarations
    ///
    /// May include declarations of external both functions and variables
    pub externs: BTreeMap<&'s str, ExternDecl<'s>>,
    /// Global variable definitions
    ///
    /// May include both top-level functions and global variables.
    /// The bindings are grouped by circularity of definitions, and
    /// the groups are ordered topologically by inter-group dependency.
    pub globals: TopologicallyOrderedDependencyGroups<'s>,
    /// Algebraic Data Type definitions
    pub adts: Adts<'s>,
}
