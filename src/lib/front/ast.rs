use super::SrcPos;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::{borrow, fmt, hash, mem};

// TODO: Replace static with const to allow matching
lazy_static!{
    pub static ref TYPE_NIL: Type<'static> = Type::Const("Nil");
    pub static ref TYPE_BOOL: Type<'static> = Type::Const("Bool");
    pub static ref TYPE_STRING: Type<'static> = Type::Const("String");
}

/// A polytype
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Poly<'src> {
    pub params: Vec<u64>,
    pub body: Type<'src>,
}

impl<'src> fmt::Display for Poly<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let params_s = self.params
            .iter()
            .map(|id| format!("${}", id))
            .intersperse(" ".to_string())
            .collect::<String>();
        write!(f, "(for ({}) {})", params_s, self.body)
    }
}

/// A type function
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

/// A type
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type<'src> {
    Var(u64),
    /// A monotype constant, like `int`, or `string`
    Const(&'src str),
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

    pub fn new_cons(car_typ: Type<'src>, cdr_typ: Type<'src>) -> Self {
        Type::App(Box::new(TypeFunc::Const("Cons")), vec![car_typ, cdr_typ])
    }

    fn is_monomorphic_in_context(&self, bound: &mut HashSet<u64>) -> bool {
        match *self {
            Type::Var(ref n) => bound.contains(n),
            Type::Const(_) => true,
            Type::App(ref f, ref args) => {
                let all_args_mono = args.iter().all(|arg| arg.is_monomorphic_in_context(bound));
                match **f {
                    TypeFunc::Const(_) => all_args_mono,
                    TypeFunc::Poly(ref p) => {
                        let mut dup = HashSet::new();
                        for param in &p.params {
                            if !bound.insert(*param) {
                                dup.insert(param);
                            }
                        }
                        let body_is_mono = p.body.is_monomorphic_in_context(bound);
                        for param in p.params.iter().filter(|param| !dup.contains(param)) {
                            bound.remove(param);
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

    pub fn get_cons(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        self.get_bin("Cons")
    }
}

impl<'src> fmt::Display for Type<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Var(id) => write!(f, "${}", id),
            Type::Const(s) => fmt::Display::fmt(s, f),
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

/// A `let` special form
#[derive(Clone, Debug)]
pub struct Let<'src> {
    pub bindings: HashMap<&'src str, Binding<'src>>,
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
pub struct Module<'src> {
    /// External variable declarations
    ///
    /// May include declarations of external both functions and variables
    pub externs: HashMap<&'src str, ExternDecl<'src>>,
    /// Global variable definitions
    ///
    /// May include both top-level functions and global variables
    pub globals: HashMap<&'src str, Binding<'src>>,
}
