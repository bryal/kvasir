use super::SrcPos;
use itertools::Itertools;
use std::borrow;
use std::collections::HashMap;
use std::fmt;
use std::hash;

lazy_static!{
    pub static ref TYPE_UNINFERRED: Type<'static> = Type::Uninferred;
    pub static ref TYPE_NIL: Type<'static> = Type::Const("Nil");
    pub static ref TYPE_BOOL: Type<'static> = Type::Const("Bool");
    pub static ref TYPE_BYTE_SLICE: Type<'static> = Type::App("Slice", vec![Type::Const("UInt8")]);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<'src> {
    Uninferred,
    /// A type variable identified by an integer, bound in a type scheme
    Var(u64),
    /// A monotype constant, like `int`, or `string`
    Const(&'src str),
    /// An application of a type function over one/some/no monotype(s)
    App(&'src str, Vec<Type<'src>>),
    /// A polymorphic type scheme
    Scheme(Vec<u64>, Box<Type<'src>>),
}

/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'src> Type<'src> {
    pub fn new_func(arg: Type<'src>, ret: Type<'src>) -> Self {
        Type::App("->", vec![arg, ret])
    }

    pub fn new_cons(car_typ: Type<'src>, cdr_typ: Type<'src>) -> Self {
        Type::App("Cons", vec![car_typ, cdr_typ])
    }

    pub fn is_unknown(&self) -> bool {
        match *self {
            Type::Uninferred => true,
            _ => false,
        }
    }
    pub fn is_partially_known(&self) -> bool {
        !self.is_unknown()
    }

    pub fn is_fully_inferred(&self) -> bool {
        match *self {
            Type::Uninferred => false,
            Type::Var(_) => true,
            Type::Const(_) => true,
            Type::App(_, ref args) => args.iter().all(Type::is_fully_inferred),
            Type::Scheme(_, _) => unimplemented!(),
        }
    }

    /// If the type is a function type signature, extract the parameter type and the return type.
    pub fn get_func_sig(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        match *self {
            Type::App("->", ref ts) => {
                assert_eq!(ts.len(), 2);
                Some((&ts[0], &ts[1]))
            }
            _ => None,
        }
    }

    pub fn get_cons(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        match *self {
            Type::App("Cons", ref ts) if ts.len() == 2 => Some((&ts[0], &ts[1])),
            _ => None,
        }
    }

    /// Recursively infer all `Uninferred` by the `by` type.
    /// If types are incompatible, e.g. `(Vec Inferred)` v. `(Option Int32)`, return `None`
    pub fn infer_by(&self, by: &Self) -> Option<Self> {
        match (self, by) {
            (_, _) if self == by => Some(self.clone()),
            (_, &Type::Uninferred) => Some(self.clone()),
            (&Type::Uninferred, _) => Some(by.clone()),
            (&Type::App(ref s1, ref as1), &Type::App(ref s2, ref as2)) if s1 == s2 => {
                as1.iter()
                    .zip(as2.iter())
                    .map(|(a1, a2)| a1.infer_by(a2))
                    .collect::<Option<_>>()
                    .map(|args| Type::App(s1.clone(), args))
            }
            (_, _) => None,
        }
    }
}

impl<'src> fmt::Display for Type<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Uninferred => write!(f, "_"),
            Type::Var(id) => write!(f, "<var {}>", id),
            Type::Const(basic) => write!(f, "{}", basic),
            Type::App(constructor, ref args) => {
                write!(
                    f,
                    "({} {})",
                    constructor,
                    args.iter().fold(String::new(), |acc, arg| {
                        format!("{} {}", acc, arg)
                    })
                )
            }
            Type::Scheme(ref vars, ref body) => {
                write!(
                    f,
                    "(forall ({}) {})",
                    vars.iter()
                        .map(|id| format!("${}", id))
                        .intersperse(" ".to_string())
                        .collect::<String>(),
                    body
                )
            }
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
pub struct StaticDef<'src> {
    pub body: Expr<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct ExternProcDecl<'src> {
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
pub struct Binding<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}

#[derive(Clone, Debug)]
pub struct Bool<'src> {
    pub val: bool,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Call<'src> {
    pub func: Expr<'src>,
    pub arg: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

impl<'src> Call<'src> {
    pub fn new_multary(func: Expr<'src>, mut args: Vec<Expr<'src>>, pos: SrcPos<'src>) -> Self {
        let last = args.pop().unwrap_or_else(|| {
            pos.error_exit("Empty argument list. Function calls can't be nullary")
        });

        let calls = args.into_iter().fold(func, |f, arg| {
            Expr::Call(Box::new(Call {
                func: f,
                arg: arg,
                typ: Type::Uninferred,
                pos: pos.clone(),
            }))
        });

        Call {
            func: calls,
            arg: last,
            typ: Type::Uninferred,
            pos: pos,
        }
    }
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

// A parameter for a function/lambda/
#[derive(Clone, Debug)]
pub struct Param<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'src> {
    pub param: Param<'src>,
    pub body: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

impl<'src> Lambda<'src> {
    pub fn new_multary(
        mut params: Vec<Param<'src>>,
        params_pos: &SrcPos<'src>,
        body: Expr<'src>,
        pos: &SrcPos<'src>,
    ) -> Self {
        let innermost = Lambda {
            param: params.pop().unwrap_or_else(|| {
                params_pos.error_exit(
                    "Empty parameter list. Functions can't be \
                                       nullary, consider defining a constant instead",
                )
            }),
            body: body,
            typ: Type::Uninferred,
            pos: pos.clone(),
        };

        params.into_iter().rev().fold(innermost, |inner, param| {
            Lambda {
                param: param,
                body: Expr::Lambda(Box::new(inner)),
                typ: Type::Uninferred,
                pos: pos.clone(),
            }
        })
    }
}

#[derive(Clone, Debug)]
pub struct Let<'src> {
    pub bindings: Vec<(Param<'src>, Expr<'src>)>,
    pub body: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

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
    Binding(Binding<'src>),
    Call(Box<Call<'src>>),
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
            Expr::Binding(ref bnd) => &bnd.ident.pos,
            Expr::Call(ref call) => &call.pos,
            Expr::If(ref cond) => &cond.pos,
            Expr::Lambda(ref l) => &l.pos,
            Expr::Let(ref l) => &l.pos,
            Expr::TypeAscript(ref a) => &a.pos,
            Expr::Cons(ref c) => &c.pos,
        }
    }

    pub fn get_type(&self) -> &Type<'src> {
        match *self {
            Expr::Nil(_) => &TYPE_NIL,
            Expr::NumLit(ref l) => &l.typ,
            Expr::StrLit(ref l) => &l.typ,
            Expr::Bool(_) => &TYPE_BOOL,
            Expr::Binding(ref bnd) => &bnd.typ,
            Expr::Call(ref call) => &call.typ,
            Expr::If(ref cond) => &cond.typ,
            Expr::Lambda(ref lam) => &lam.typ,
            Expr::Let(ref l) => &l.typ,
            // The existance of a type ascription implies that the expression has not yet been
            // inferred. As such, return type `Uninferred` to imply that inference is needed
            Expr::TypeAscript(_) => &TYPE_UNINFERRED,
            Expr::Cons(ref c) => &c.typ,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Module<'src> {
    pub static_defs: HashMap<&'src str, StaticDef<'src>>,
    pub extern_funcs: HashMap<&'src str, ExternProcDecl<'src>>,
}
