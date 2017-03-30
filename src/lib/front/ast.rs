
use std::borrow;
use std::collections::HashMap;
use std::fmt;
use std::hash;
use super::SrcPos;

lazy_static!{
    pub static ref TYPE_UNKNOWN: Type<'static> = Type::Unknown;
    pub static ref TYPE_NIL: Type<'static> = Type::Basic("Nil");
    pub static ref TYPE_BOOL: Type<'static> = Type::Basic("Bool");
    pub static ref TYPE_BYTE_SLICE: Type<'static> = Type::Construct("Slice",
                                                                    vec![Type::Basic("UInt8")]);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<'src> {
    Unknown,
    Basic(&'src str),
    Construct(&'src str, Vec<Type<'src>>),
}
/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'src> Type<'src> {
    pub fn new_proc(mut arg_tys: Vec<Type<'src>>, return_ty: Type<'src>) -> Self {
        arg_tys.push(return_ty);
        Type::Construct("Proc", arg_tys)
    }

    pub fn new_cons(car_typ: Type<'src>, cdr_typ: Type<'src>) -> Self {
        Type::Construct("Cons", vec![car_typ, cdr_typ])
    }

    pub fn is_unknown(&self) -> bool {
        match *self {
            Type::Unknown => true,
            _ => false,
        }
    }
    pub fn is_partially_known(&self) -> bool {
        !self.is_unknown()
    }
    pub fn is_fully_known(&self) -> bool {
        match *self {
            Type::Unknown => false,
            Type::Basic(_) => true,
            Type::Construct(_, ref args) => args.iter().all(Type::is_fully_known),
        }
    }

    /// If the type is a procedure type signature, extract the parameter types and the return type.
    pub fn get_proc_sig(&self) -> Option<(&[Type<'src>], &Type<'src>)> {
        match *self {
            Type::Construct("Proc", ref ts) => {
                Some(ts.split_last()
                       .map(|(b, ps)| (ps, b))
                       .expect("ICE: `Proc` construct with no arguments"))
            }
            _ => None,
        }
    }

    pub fn get_cons(&self) -> Option<(&Type<'src>, &Type<'src>)> {
        match *self {
            Type::Construct("Cons", ref ts) if ts.len() == 2 => Some((&ts[0], &ts[1])),
            _ => None,
        }
    }

    /// Recursively infer all `Unknown` by the `by` type.
    /// If types are incompatible, e.g. `(Vec Inferred)` v. `(Option Int32)`, return `None`
    pub fn infer_by(&self, by: &Self) -> Option<Self> {
        match (self, by) {
            (_, _) if self == by => Some(self.clone()),
            (_, &Type::Unknown) => Some(self.clone()),
            (&Type::Unknown, _) => Some(by.clone()),
            (&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 => {
                as1.iter()
                   .zip(as2.iter())
                   .map(|(a1, a2)| a1.infer_by(a2))
                   .collect::<Option<_>>()
                   .map(|args| Type::Construct(s1.clone(), args))
            }
            (_, _) => None,
        }
    }
}
impl<'src> fmt::Display for Type<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Unknown => write!(f, "_"),
            Type::Basic(basic) => write!(f, "{}", basic),
            Type::Construct(constructor, ref args) => {
                write!(f,
                       "({} {})",
                       constructor,
                       args.iter().fold(String::new(), |acc, arg| format!("{} {}", acc, arg)))
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
    pub proced: Expr<'src>,
    pub args: Vec<Expr<'src>>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Block<'src> {
    pub static_defs: HashMap<&'src str, StaticDef<'src>>,
    pub extern_funcs: HashMap<&'src str, ExternProcDecl<'src>>,
    pub exprs: Vec<Expr<'src>>,
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

// A parameter for a function/lambda/procedure
#[derive(Clone, Debug)]
pub struct Param<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}
impl<'src> Param<'src> {
    pub fn new(ident: Ident<'src>, typ: Type<'src>) -> Param<'src> {
        Param { ident: ident, typ: typ }
    }
}

#[derive(Clone, Debug)]
pub struct Lambda<'src> {
    pub params: Vec<Param<'src>>,
    pub body: Expr<'src>,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Assign<'src> {
    pub lhs: Expr<'src>,
    pub rhs: Expr<'src>,
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
    Block(Box<Block<'src>>),
    If(Box<If<'src>>),
    Lambda(Box<Lambda<'src>>),
    Assign(Box<Assign<'src>>),
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
            Expr::Block(ref block) => &block.pos,
            Expr::If(ref cond) => &cond.pos,
            Expr::Lambda(ref l) => &l.pos,
            Expr::Assign(ref a) => &a.pos,
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
            Expr::Block(ref block) => &block.typ,
            Expr::If(ref cond) => &cond.typ,
            Expr::Lambda(ref lam) => &lam.typ,
            Expr::Assign(ref assign) => &assign.typ,
            // The existance of a type ascription implies that the expression has not yet been
            // inferred. As such, return type `Unknown` to imply that inference is needed
            Expr::TypeAscript(_) => &TYPE_UNKNOWN,
            Expr::Cons(ref c) => &c.typ,
        }
    }
}

/// Represents an item, i.e. a use-statement or a definition or some such
pub enum Item<'src> {
    StaticDef(Ident<'src>, StaticDef<'src>),
    ExternProcDecl(Ident<'src>, ExternProcDecl<'src>),
    Expr(Expr<'src>),
}

#[derive(Clone, Debug)]
pub struct Module<'src> {
    pub static_defs: HashMap<&'src str, StaticDef<'src>>,
    pub extern_funcs: HashMap<&'src str, ExternProcDecl<'src>>,
}
