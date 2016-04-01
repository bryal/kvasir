// The MIT License (MIT)
//
// Copyright (c) 2015 Johan Johansson
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::fmt;
use std::collections::HashMap;
use std::hash;
use std::borrow::{self, Cow};
use super::SrcPos;

lazy_static!{
	pub static ref TYPE_UNKNOWN: Type<'static> = Type::Unknown;
	pub static ref TYPE_NIL: Type<'static> = Type::Basic("Nil");
	pub static ref TYPE_BOOL: Type<'static> = Type::Basic("Bool");
	pub static ref TYPE_SYMBOL: Type<'static> = Type::Basic("Symbol");
	pub static ref TYPE_BYTE_SLICE: Type<'static> = Type::Construct(
		"Slice",
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
    pub fn get_proc_sig<'t>(&'t self) -> Option<(&'t [Type<'src>], &'t Type<'src>)> {
        match *self {
            Type::Construct("Proc", ref ts) => {
                Some(ts.split_last()
                       .map(|(b, ps)| (ps, b))
                       .expect("ICE: `Proc` construct with no arguments"))
            }
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
            (&Type::Construct(ref s1, ref as1),
             &Type::Construct(ref s2, ref as2))
                if s1 == s2 => {
                as1.iter()
                   .zip(as2.iter())
                   .map(|(a1, a2)| a1.infer_by(a2))
                   .collect::<Option<_>>()
                   .map(|args| Type::Construct(s1.clone(), args))
            }
            (_, _) => None,
        }
    }

    /// Returns whether this is an integer type
    pub fn is_int(&self) -> bool {
        match *self {
            Type::Basic("Int8") |
            Type::Basic("Int16") |
            Type::Basic("Int32") |
            Type::Basic("Int64") |
            Type::Basic("IntPtr") |
            Type::Basic("UInt8") |
            Type::Basic("UInt16") |
            Type::Basic("UInt32") |
            Type::Basic("UInt64") |
            Type::Basic("UIntPtr") => true,
            _ => false,
        }
    }

    /// Returns whether this is a pointer type
    pub fn is_ptr(&self) -> bool {
        match *self {
            Type::Construct("RawPtr", _) => true,
            _ => false,
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

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Path<'src> {
    parts: Vec<&'src str>,
    is_absolute: bool,
    pub pos: SrcPos<'src>,
}
impl<'src> Path<'src> {
    pub fn is_absolute(&self) -> bool {
        self.is_absolute
    }

    /// If self is just a simple ident, return it as Some
    pub fn as_ident(&self) -> Option<&str> {
        if !self.is_absolute && self.parts.len() == 1 {
            Some(*self.parts.first().unwrap())
        } else {
            None
        }
    }

    /// Concatenates two paths.
    ///
    /// Returns both `self` as `Err` if right hand path is absolute
    pub fn concat(mut self, other: &Self) -> Result<Self, Self> {
        if other.is_absolute {
            Err(self)
        } else {
            self.parts.extend(other.parts.iter());
            Ok(self)
        }
    }

    pub fn to_string(&self) -> String {
        format!("{}{}{}",
                if self.is_absolute() {
                    "\\"
                } else {
                    ""
                },
                self.parts[0],
                self.parts[1..].iter().fold(String::new(), |acc, p| acc + "\\" + p))
    }

    pub fn from_str(path_str: &'src str, pos: SrcPos<'src>) -> Self {
        let (is_absolute, path_str) = if path_str.ends_with("\\") {
            pos.error("Path ends with `\\`")
        } else if path_str.starts_with('\\') {
            if path_str.len() == 1 {
                pos.error("Path is a lone `\\`")
            }
            (true, &path_str[1..])
        } else {
            (false, path_str)
        };

        Path {
            parts: path_str.split('\\')
                           .map(|part| {
                               if part == "" {
                                   pos.error("Invalid path")
                               } else {
                                   part
                               }
                           })
                           .collect(),
            is_absolute: is_absolute,
            pos: pos,
        }
    }
}
impl<'src> PartialEq<str> for Path<'src> {
    fn eq(&self, rhs: &str) -> bool {
        self.to_string() == rhs
    }
}

#[derive(Clone, Debug)]
pub struct Use<'src> {
    pub path: Path<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct ConstDef<'src> {
    pub body: Expr<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Nil<'src> {
    pub typ: Type<'src>,
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
    pub path: Path<'src>,
    pub typ: Type<'src>,
}

#[derive(Clone, Debug)]
pub struct Bool<'src> {
    pub val: bool,
    pub typ: Type<'src>,
    pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Call<'src> {
    pub proced: Expr<'src>,
    pub args: Vec<Expr<'src>>,
    pub pos: SrcPos<'src>,
}
impl<'src> Call<'src> {
    pub fn get_type(&self) -> Cow<Type<'src>> {
        let proc_typ = self.proced.get_type();

        if proc_typ.is_unknown() {
            Cow::Borrowed(&TYPE_UNKNOWN)
        } else {
            let maybe_body = match self.proced.get_type() {
                Cow::Borrowed(typ) => {
                    typ.get_proc_sig()
                       .map(|(_, body)| Cow::Borrowed(body))
                }
                Cow::Owned(typ) => {
                    typ.get_proc_sig()
                       .map(|(_, body)| Cow::Owned(body.clone()))
                }
            };

            maybe_body.expect("ICE: Call::get_type: get_proc_sig returned None")
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block<'src> {
    pub uses: Vec<Use<'src>>,
    pub const_defs: HashMap<Ident<'src>, ConstDef<'src>>,
    pub extern_funcs: HashMap<Ident<'src>, Type<'src>>,
    pub exprs: Vec<Expr<'src>>,
    pub pos: SrcPos<'src>,
}
impl<'src> Block<'src> {
    fn get_type(&self) -> Cow<Type<'src>> {
        self.exprs.last().unwrap().get_type()
    }
}

/// if-then-else expression
#[derive(Clone, Debug)]
pub struct If<'src> {
    pub predicate: Expr<'src>,
    pub consequent: Expr<'src>,
    pub alternative: Expr<'src>,
    pub pos: SrcPos<'src>,
}
impl<'src> If<'src> {
    fn get_type(&self) -> Cow<Type<'src>> {
        self.consequent.get_type()
    }
}

// A parameter for a function/lambda/procedure
#[derive(Clone, Debug)]
pub struct Param<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}
impl<'src> Param<'src> {
    pub fn new(ident: Ident<'src>, typ: Type<'src>) -> Param<'src> {
        Param {
            ident: ident,
            typ: typ,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lambda<'src> {
    pub params: Vec<Param<'src>>,
    pub body: Expr<'src>,
    pub pos: SrcPos<'src>,
}
impl<'src> Lambda<'src> {
    pub fn get_type(&self) -> Type<'src> {
        Type::new_proc(self.params.iter().map(|p| p.typ.clone()).collect(),
                       self.body.get_type().into_owned())
    }
}

#[derive(Clone, Debug)]
pub struct VarDef<'src> {
    pub binding: Ident<'src>,
    pub mutable: bool,
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
pub struct Symbol<'src> {
    pub ident: Ident<'src>,
    pub typ: Type<'src>,
}

#[derive(Clone, Debug)]
pub struct Deref<'src> {
    pub r: Expr<'src>,
    pub pos: SrcPos<'src>,
}
impl<'src> Deref<'src> {
    pub fn get_type(&self) -> Cow<Type<'src>> {
        match self.r.get_type() {
            Cow::Owned(Type::Construct("RawPtr", ref args)) => {
                Cow::Owned(args.first().cloned().unwrap_or_else(|| unreachable!()))
            }
            Cow::Borrowed(&Type::Construct("RawPtr", ref args)) => {
                Cow::Borrowed(args.first().unwrap_or_else(|| unreachable!()))
            }
            ref t if **t == Type::Unknown => Cow::Borrowed(&TYPE_UNKNOWN),
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Transmute<'src> {
    pub arg: Expr<'src>,
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
    VarDef(Box<VarDef<'src>>),
    Assign(Box<Assign<'src>>),
    Symbol(Symbol<'src>),
    Deref(Box<Deref<'src>>),
    Transmute(Box<Transmute<'src>>),
    /// Type ascription. E.g. `(:Int32 42)`
    TypeAscript(Box<TypeAscript<'src>>),
}
impl<'src> Expr<'src> {
    /// Returns whether this expression is a variable definition
    pub fn is_var_def(&self) -> bool {
        if let &Expr::VarDef(_) = self {
            true
        } else {
            false
        }
    }

    pub fn pos(&self) -> &SrcPos<'src> {
        match *self {
            Expr::Nil(ref n) => &n.pos,
            Expr::NumLit(ref l) => &l.pos,
            Expr::StrLit(ref l) => &l.pos,
            Expr::Bool(ref b) => &b.pos,
            Expr::Binding(ref bnd) => &bnd.path.pos,
            Expr::Call(ref call) => &call.pos,
            Expr::Block(ref block) => &block.pos,
            Expr::If(ref cond) => &cond.pos,
            Expr::Lambda(ref l) => &l.pos,
            Expr::VarDef(ref def) => &def.pos,
            Expr::Assign(ref a) => &a.pos,
            Expr::Symbol(ref s) => &s.ident.pos,
            Expr::Deref(ref deref) => &deref.pos,
            Expr::Transmute(ref trans) => &trans.pos,
            Expr::TypeAscript(ref a) => &a.pos,
        }
    }

    pub fn get_type(&self) -> Cow<Type<'src>> {
        match *self {
            Expr::Nil(ref n) => Cow::Borrowed(&n.typ),
            Expr::NumLit(ref l) => Cow::Borrowed(&l.typ),
            Expr::StrLit(ref l) => Cow::Borrowed(&l.typ),
            Expr::Bool(ref b) => Cow::Borrowed(&b.typ),
            Expr::Binding(ref bnd) => Cow::Borrowed(&bnd.typ),
            Expr::Call(ref call) => call.get_type(),
            Expr::Block(ref block) => block.get_type(),
            Expr::If(ref cond) => cond.get_type(),
            Expr::Lambda(ref lam) => Cow::Owned(lam.get_type()),
            Expr::VarDef(ref def) => Cow::Borrowed(&def.typ),
            Expr::Assign(ref assign) => Cow::Borrowed(&assign.typ),
            Expr::Symbol(ref sym) => Cow::Borrowed(&sym.typ),
            Expr::Deref(ref deref) => deref.get_type(),
            Expr::Transmute(ref trans) => Cow::Borrowed(&trans.typ),
            // The existance of a type ascription implies that the expression has not yet been
            // inferred. As such, return type `Unknown` to imply that inference is needed
            Expr::TypeAscript(_) => Cow::Borrowed(&TYPE_UNKNOWN),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Module<'src> {
    pub uses: Vec<Use<'src>>,
    pub const_defs: HashMap<Ident<'src>, ConstDef<'src>>,
    pub extern_funcs: HashMap<Ident<'src>, Type<'src>>,
}
