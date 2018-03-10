//! The concrete syntax tree
//!
//! The syntax tree that the lexer produces

use lib::front::SrcPos;
use itertools::Itertools;
use std::borrow::Cow;
use std::fmt;

/// A tree of syntax items (Concrete Syntax Tree),
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cst<'s> {
    /// An S-Expression.
    Sexpr(Vec<Cst<'s>>, SrcPos<'s>),
    /// An identifier.
    Ident(&'s str, SrcPos<'s>),
    /// A numeric literal.
    Num(&'s str, SrcPos<'s>),
    /// A string literal.
    Str(Cow<'s, str>, SrcPos<'s>),
}

impl<'s> Cst<'s> {
    pub fn pos(&self) -> &SrcPos<'s> {
        match *self {
            Cst::Sexpr(_, ref p)
            | Cst::Ident(_, ref p)
            | Cst::Num(_, ref p)
            | Cst::Str(_, ref p) => p,
        }
    }
}

impl<'s> fmt::Display for Cst<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Cst::Ident(s, _) | Cst::Num(s, _) => write!(f, "{}", s),
            Cst::Str(ref s, _) => write!(f, "{}", s),
            Cst::Sexpr(ref v, _) => write!(
                f,
                "({})",
                v.iter()
                    .map(|e| e.to_string())
                    .intersperse(" ".into())
                    .collect::<String>()
            ),
        }
    }
}
