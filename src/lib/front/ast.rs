use super::SrcPos;
use itertools::{Itertools, zip};
use std::collections::{HashMap, BTreeMap, BTreeSet, HashSet};
use std::{borrow, fmt, hash, mem, path};
use std::iter::once;

// TODO: Replace static with const to allow matching
lazy_static!{
    pub static ref TYPE_NIL: Type<'static> = Type::Const("Nil", None);
    pub static ref TYPE_BOOL: Type<'static> = Type::Const("Bool", None);
    pub static ref TYPE_STRING: Type<'static> = Type::new_cons(
        Type::Const("UIntPtr", None),
        Type::new_ptr(Type::Const("UInt8", None)));
    pub static ref TYPE_REALWORLD: Type<'static> = Type::Const("RealWorld", None);
}

/// A polytype
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poly<'src> {
    pub params: Vec<TVar<'src>>,
    pub body: Type<'src>,
}

impl<'src> fmt::Display for Poly<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let params_s = self.params
            .iter()
            .map(|tv| {
                format!(
                    "(: ${} {})",
                    tv.id,
                    tv.constrs
                        .iter()
                        .cloned()
                        .intersperse(" ")
                        .collect::<String>()
                )
            })
            .intersperse(" ".to_string())
            .collect::<String>();
        write!(f, "(for ({}) {})", params_s, self.body)
    }
}

/// A type function
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeFunc<'src> {
    Const(&'src str),
    Poly(Poly<'src>),
}

impl<'src> fmt::Display for TypeFunc<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeFunc::Const(s) => fmt::Display::fmt(s, f),
            TypeFunc::Poly(ref p) => fmt::Display::fmt(p, f),
        }
    }
}

/// A type variable uniquely identified by an integer id
/// and constrained by a set of type classes
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TVar<'src> {
    /// A unique identifier
    pub id: u64,
    /// A set of constraints that applies to the polytype
    pub constrs: BTreeSet<&'src str>,
    /// Whether the variable is explicit in source, and if so, what it's name is
    ///
    /// The variable being explicit implies that it is immutable.
    /// If a more specific type is encountered during inference, do not unify to the more
    /// explicit type, but instead produce an error.
    pub explicit: Option<&'src str>,
}

impl<'src> fmt::Display for TVar<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tv = format!("${}", self.id);
        let name = self.explicit.unwrap_or(&tv);
        if self.constrs.is_empty() {
            write!(f, "{}", name)
        } else {
            write!(
                f,
                "(: {} {})",
                name,
                self.constrs
                    .iter()
                    .cloned()
                    .intersperse(" ")
                    .collect::<String>()
            )
        }
    }
}

// TODO: This is weird. Probably wrong. Each type variable should not carry constraints?
//       optionally being explicit kind of makes sense though, but maybe explicit, locked
//       type variables should be a discinct variant?

/// A type
#[derive(Clone, Debug, PartialOrd, Ord, Hash)]
pub enum Type<'src> {
    /// A type variable uniquely identified by an integer id
    /// and constrained by a set of type classes
    Var(TVar<'src>),
    /// A monotype constant, like `int`, or `string`
    Const(&'src str, Option<SrcPos<'src>>),
    /// An application of a type function over one/some/no monotype(s)
    App(Box<TypeFunc<'src>>, Vec<Type<'src>>),
    /// A polytype
    Poly(Box<Poly<'src>>),
}

/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'src> Type<'src> {
    pub fn new_func(arg: Type<'src>, ret: Type<'src>) -> Self {
        Type::App(Box::new(TypeFunc::Const("->")), vec![arg, ret])
    }

    pub fn new_io(ret: Type<'src>) -> Self {
        Type::new_func(
            TYPE_REALWORLD.clone(),
            Type::new_cons(ret, TYPE_REALWORLD.clone()),
        )
    }

    pub fn new_cons(car_typ: Type<'src>, cdr_typ: Type<'src>) -> Self {
        Type::App(Box::new(TypeFunc::Const("Cons")), vec![car_typ, cdr_typ])
    }

    pub fn new_ptr(typ: Type<'src>) -> Self {
        Type::App(Box::new(TypeFunc::Const("Ptr")), vec![typ])
    }

    pub fn new_binop(typ: Type<'src>) -> Self {
        Type::new_func(Type::new_cons(typ.clone(), typ.clone()), typ)
    }

    pub fn new_relational_binop(typ: Type<'src>) -> Self {
        Type::new_func(Type::new_cons(typ.clone(), typ), Type::Const("Bool", None))
    }

    pub fn new_logic_binop() -> Self {
        Type::new_func(
            Type::new_cons(Type::Const("Bool", None), Type::Const("Bool", None)),
            Type::Const("Bool", None),
        )
    }

    /// If this type is an instantiated polytype, return the instantiation args
    pub fn get_inst_args(&self) -> Option<&[Type<'src>]> {
        match *self {
            Type::App(box TypeFunc::Poly(_), ref args) => Some(args),
            _ => None,
        }
    }

    fn is_monomorphic_in_context(&self, bound: &mut HashSet<u64>) -> bool {
        match *self {
            Type::Var(ref v) => bound.contains(&v.id),
            Type::Const(_, _) => true,
            Type::App(ref f, ref args) => {
                let all_args_mono = args.iter().all(|arg| arg.is_monomorphic_in_context(bound));
                match **f {
                    TypeFunc::Const(_) => all_args_mono,
                    TypeFunc::Poly(ref p) => {
                        let mut dup = HashSet::new();
                        for &TVar { id: param, .. } in &p.params {
                            if !bound.insert(param) {
                                dup.insert(param);
                            }
                        }
                        let body_is_mono = p.body.is_monomorphic_in_context(bound);
                        for param in p.params.iter().filter(|&param| !dup.contains(&param.id)) {
                            bound.remove(&param.id);
                        }
                        all_args_mono && body_is_mono
                    }
                }
            }
            Type::Poly(ref p) => p.params.is_empty() && p.body.is_monomorphic_in_context(bound),
        }
    }

    /// Returns whether type is completly monomorphic
    pub fn is_monomorphic(&self) -> bool {
        self.is_monomorphic_in_context(&mut HashSet::new())
    }

    pub fn canonicalize_in_context(&self, s: &mut HashMap<u64, Type<'src>>) -> Type<'src> {
        match *self {
            Type::Const(_, _) => self.clone(),
            Type::Var(ref v) => s.get(&v.id).unwrap_or(self).clone(),
            Type::App(box TypeFunc::Const(c), ref args) => {
                Type::App(
                    Box::new(TypeFunc::Const(c)),
                    args.iter()
                        .map(|arg| arg.canonicalize_in_context(s))
                        .collect(),
                )
            }
            Type::App(box TypeFunc::Poly(ref p), ref args) => {
                let shadoweds = zip(&p.params, args)
                    .filter_map(|(param, arg)| {
                        s.insert(param.id, arg.clone()).map(|shad| (param.id, shad))
                    })
                    .collect::<Vec<_>>();
                let b = p.body.canonicalize_in_context(s);
                s.extend(shadoweds);
                b
            }
            Type::Poly(ref p) => {
                Type::Poly(Box::new(Poly {
                    params: p.params.clone(),
                    body: p.body.canonicalize_in_context(s),
                }))
            }
        }
    }

    /// Recursively apply applications to polytypes
    ///
    /// # Examples
    /// `canonicalize (app (poly (t u) (-> t u)) Int Float) == (-> Int Float)`
    pub fn canonicalize(&self) -> Type<'src> {
        self.canonicalize_in_context(&mut HashMap::new())
    }

    /// If a type constant, return the name
    pub fn get_const(&self) -> Option<&'src str> {
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
    pub fn num_to_int64(&self) -> Self {
        match *self {
            Type::Var(TVar { ref constrs, .. })
                if constrs.len() == 1 && constrs.contains("Num") => Type::Const("Int64", None),
            _ => self.clone(),
        }
    }

    fn get_bin(&self, con: &'src str) -> Option<(&Type<'src>, &Type<'src>)> {
        match *self {
            Type::App(ref f, ref ts) if **f == TypeFunc::Const(con) => {
                assert_eq!(ts.len(), 2);
                Some((&ts[0], &ts[1]))
            }
            _ => None,
        }
    }

    /// If the type is a function type signature, extract the parameter type and the return type.
    pub fn get_func(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        self.get_bin("->")
    }

    /// If the type is of the form `(-> (Cons A B) C)`, return the tuple `(A, B, C)`
    pub fn get_cons_binary_func(&self) -> Option<(&Type<'src>, &Type<'src>, &Type<'src>)> {
        self.get_func().and_then(
            |(c, r)| c.get_cons().map(|(a, b)| (a, b, r)),
        )
    }

    /// If binop, by the definition of binops as : S x S -> S, return the operand type
    pub fn get_cons_binop(&self) -> Option<&Self> {
        if let Some((a, b, r)) = self.get_cons_binary_func() {
            if a == b && b == r { Some(a) } else { None }
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

    pub fn get_cons(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        self.get_bin("Cons")
    }

    pub fn fulfills_constraints(&self, cs: &BTreeSet<&str>) -> bool {
        use self::Type::*;
        cs.iter().all(|c| match *c {
            "Num" => {
                match *self {
                    Const("Int8", _) |
                    Const("Int16", _) |
                    Const("Int32", _) |
                    Const("Int64", _) |
                    Const("IntPtr", _) |
                    Const("UInt8", _) |
                    Const("UInt16", _) |
                    Const("UInt32", _) |
                    Const("UInt64", _) |
                    Const("UIntPtr", _) |
                    Const("Bool", _) |
                    Const("Float32", _) |
                    Const("Float64", _) => true,
                    _ => false,
                }
            }
            _ => unimplemented!(),
        })
    }
}

impl<'src> PartialEq for Type<'src> {
    fn eq(&self, other: &Self) -> bool {
        use self::Type::*;
        match (self, other) {
            (&Var(ref v1), &Var(ref v2)) => {
                v1.id == v2.id && v1.constrs == v2.constrs && v1.explicit == v2.explicit
            }
            (&Const(t, _), &Const(u, _)) => t == u,
            (&App(ref f, ref v), &App(ref g, ref w)) => f == g && v == w,
            (&Poly(ref p), &Poly(ref q)) => p == q,
            _ => false,
        }
    }
}

impl<'src> Eq for Type<'src> {}

impl<'src> fmt::Display for Type<'src> {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident<'src> {
    pub s: &'src str,
    pub pos: SrcPos<'src>,
}
impl<'src> Ident<'src> {
    pub fn new(s: &'src str, pos: SrcPos<'src>) -> Ident<'src> {
        Ident { s: s, pos: pos }
    }
}
impl<'src> PartialEq<str> for Ident<'src> {
    fn eq(&self, rhs: &str) -> bool {
        self.s == rhs
    }
}
impl<'src> hash::Hash for Ident<'src> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.s.hash(state);
    }
}
impl<'src> borrow::Borrow<str> for Ident<'src> {
    fn borrow(&self) -> &str {
        &self.s
    }
}
impl<'src> fmt::Display for Ident<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.s, f)
    }
}

#[derive(Clone, Debug)]
pub struct ExternDecl<'src> {
    pub ident: Ident<'src>,
    /// The type of the external variable being declared.
    ///
    /// Guaranteed during parsing to be monomorphic and canonical
    /// I.e. no type variables or polytype applications
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Nil<'src> {
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct NumLit<'src> {
    pub lit: &'src str,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct StrLit<'src> {
    pub lit: borrow::Cow<'src, str>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Variable<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}

#[derive(Clone, Debug)]
pub struct Bool<'src> {
    pub val: bool,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct App<'src> {
    pub func: Expr<'src>,
    pub arg: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

/// if-then-else expression
#[derive(Clone, Debug)]
pub struct If<'src> {
    pub predicate: Expr<'src>,
    pub consequent: Expr<'src>,
    pub alternative: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'src> {
    pub param_ident: Ident<'src>,
    pub param_type: Type<'src>,
    pub body: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

/// A binding of a name to a value, i.e. a variable definition.
#[derive(Clone, Debug)]
pub struct Binding<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
    pub val: Expr<'src>,
    /// If this binding is polymorphic, here will be mappings from
    /// application arguments to monomorphic instantiation of `val`
    pub mono_insts: HashMap<Vec<Type<'src>>, Expr<'src>>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub enum Group<'src> {
    Circular(HashMap<&'src str, Binding<'src>>),
    Uncircular(&'src str, Binding<'src>),
}

impl<'src> Group<'src> {
    pub fn contains(&self, e: &str) -> bool {
        match *self {
            Group::Circular(ref xs) => xs.contains_key(e),
            Group::Uncircular(x, _) => e == x,
        }
    }

    pub fn ids<'a>(&'a self) -> Box<Iterator<Item = &'src str> + 'a> {
        match *self {
            Group::Circular(ref xs) => Box::new(xs.keys().map(|s| *s)),
            Group::Uncircular(x, _) => Box::new(once(x)),
        }
    }

    pub fn bindings<'s>(&'s self) -> Box<Iterator<Item = &'s Binding<'src>> + 's> {
        match *self {
            Group::Circular(ref xs) => Box::new(xs.iter().map(|(_, b)| b)),
            Group::Uncircular(_, ref b) => Box::new(once(b)),
        }
    }

    pub fn bindings_mut<'s>(&'s mut self) -> Box<Iterator<Item = &'s mut Binding<'src>> + 's> {
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
#[derive(Clone, Debug)]
pub struct TopologicallyOrderedDependencyGroups<'src>(pub Vec<Group<'src>>);

impl<'src> TopologicallyOrderedDependencyGroups<'src> {
    pub fn ids<'a>(&'a self) -> Box<Iterator<Item = &'src str> + 'a> {
        Box::new(self.groups().flat_map(|g| g.ids()))
    }

    /// Returns an iterator of bindings from the root of the topological order
    pub fn bindings<'s>(&'s self) -> Box<DoubleEndedIterator<Item = &'s Binding<'src>> + 's> {
        Box::new(
            self.groups()
                .flat_map(|g| g.bindings())
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    /// Returns an iterator bindings from the root of the topological order
    pub fn bindings_mut<'s>(
        &'s mut self,
    ) -> Box<DoubleEndedIterator<Item = &'s mut Binding<'src>> + 's> {
        Box::new(
            self.groups_mut()
                .flat_map(|g| g.bindings_mut())
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    /// Returns an iterator of groups from the root of the topological order
    pub fn groups<'s>(&'s self) -> Box<DoubleEndedIterator<Item = &'s Group<'src>> + 's> {
        Box::new(self.0.iter())
    }

    /// Returns an iterator of groups from the root of the topological order
    pub fn groups_mut<'s>(
        &'s mut self,
    ) -> Box<DoubleEndedIterator<Item = &'s mut Group<'src>> + 's> {
        Box::new(self.0.iter_mut())
    }
}

/// A `let` special form
#[derive(Clone, Debug)]
pub struct Let<'src> {
    pub bindings: TopologicallyOrderedDependencyGroups<'src>,
    pub body: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

/// A type ascription.
///
/// Ascribes a specific type to an expression
#[derive(Clone, Debug)]
pub struct TypeAscript<'src> {
    pub typ: Type<'src>,
    pub expr: Expr<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Cons<'src> {
    pub typ: Type<'src>,
    pub car: Expr<'src>,
    pub cdr: Expr<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Car<'src> {
    pub typ: Type<'src>,
    pub expr: Expr<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'src> {
    pub typ: Type<'src>,
    pub expr: Expr<'src>,
    pub pos: SrcPos<'src>,
}

/// A type cast
#[derive(Clone, Debug)]
pub struct Cast<'src> {
    pub expr: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub enum Expr<'src> {
    Nil(Nil<'src>),
    NumLit(NumLit<'src>),
    StrLit(StrLit<'src>),
    Bool(Bool<'src>),
    Variable(Variable<'src>),
    App(Box<App<'src>>),
    If(Box<If<'src>>),
    Lambda(Box<Lambda<'src>>),
    Let(Box<Let<'src>>),
    TypeAscript(Box<TypeAscript<'src>>),
    Cons(Box<Cons<'src>>),
    Car(Box<Car<'src>>),
    Cdr(Box<Cdr<'src>>),
    Cast(Box<Cast<'src>>),
}

impl<'src> Expr<'src> {
    pub fn pos(&self) -> &SrcPos<'src> {
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
        }
    }

    pub fn as_var(&self) -> Option<&Variable<'src>> {
        match *self {
            Expr::Variable(ref bnd) => Some(bnd),
            _ => None,
        }
    }

    pub fn get_type(&self) -> &Type<'src> {
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
    pub fn remove_type_ascription(&mut self) -> Option<Type<'src>> {
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

/// A module of definitions and declarations of functions and variables
#[derive(Clone, Debug)]
pub struct Ast<'src> {
    /// External variable declarations
    ///
    /// May include declarations of external both functions and variables
    pub externs: BTreeMap<&'src str, ExternDecl<'src>>,
    /// Global variable definitions
    ///
    /// May include both top-level functions and global variables.
    /// The bindings are grouped by circularity of definitions, and
    /// the groups are ordered topologically by inter-group dependency.
    pub globals: TopologicallyOrderedDependencyGroups<'src>,
}
