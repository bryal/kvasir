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
use std::borrow;
use super::SrcPos;

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
	pub fn nil() -> Self { Type::Basic("Nil") }

	pub fn is_unknown(&self) -> bool {
		match *self {
			Type::Unknown => true,
			_ => false
		}
	}
	pub fn is_partially_known(&self) -> bool {
		! self.is_unknown()
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
			Type::Construct("Proc", ref ts) => Some(
				ts.split_last()
					.map(|(b, ps)| (ps, b))
					.expect("ICE: `proc` construct with no arguments")),
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
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				as1.iter()
					.zip(as2.iter())
					.map(|(a1, a2)| a1.infer_by(a2))
					.collect::<Option<_>>()
					.map(|args| Type::Construct(s1.clone(), args)),
			(_, _) => None,
		}
	}
}
impl<'src> fmt::Display for Type<'src> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Type::Unknown => write!(f, "_"),
			Type::Basic(basic) => write!(f, "{}", basic),
			Type::Construct(constructor, ref args) => write!(f, "({} {})",
				constructor,
				args.iter().fold(String::new(), |acc, arg| format!("{} {}", acc, arg))),
		}
	}
}

/// An identifier
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident<'src> {
	pub s: &'src str,
	pub pos: SrcPos<'src>
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
	pub pos: SrcPos<'src>
}
impl<'src> Path<'src> {
	pub fn is_absolute(&self) -> bool { self.is_absolute }

	/// If self is just a simple ident, return it as Some
	pub fn ident(&self) -> Option<&str> {
		if ! self.is_absolute { self.parts.first().map(|&s| s) } else { None }
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
			if self.is_absolute() { "\\" } else { "" },
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

		Path{
			parts: path_str.split('\\')
				.map(|part| if part == "" {
					pos.error("Invalid path")
				} else {
					part
				})
				.collect(),
			is_absolute: is_absolute,
			pos: pos
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
	pub paths: Vec<Path<'src>>,
	pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct ConstDef<'src> {
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Call<'src> {
	pub proced: ExprMeta<'src>,
	pub args: Vec<ExprMeta<'src>>,
	pub pos: SrcPos<'src>,
}
impl<'src> Call<'src> {
	pub fn body_type(&self) -> &Type<'src> {
		self.proced.typ.get_proc_sig().expect("ICE: Call::body_type: get_proc_sig returned None").1
	}
}

#[derive(Clone, Debug)]
pub struct Block<'src> {
	pub uses: Vec<Use<'src>>,
	pub const_defs: HashMap<Ident<'src>, ConstDef<'src>>,
	pub extern_funcs: HashMap<Ident<'src>, Type<'src>>,
	pub exprs: Vec<ExprMeta<'src>>,
	pub pos: SrcPos<'src>
}

/// if-then-else expression
#[derive(Clone, Debug)]
pub struct If<'src> {
	pub predicate: ExprMeta<'src>,
	pub consequent: ExprMeta<'src>,
	pub alternative: ExprMeta<'src>,
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
		Param {
			ident: ident,
			typ: typ,
		}
	}
}

// TODO: Add support for capturing all args as a list, like `(lambda all-eq xs (for-all xs eq))`
//       for variadic expressions like `(all-eq a b c d)`
#[derive(Clone, Debug)]
pub struct Lambda<'src> {
	pub params: Vec<Param<'src>>,
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}
impl<'src> Lambda<'src> {
	pub fn get_type(&self) -> Type<'src> {
		Type::new_proc(
			self.params.iter().map(|p| p.typ.clone()).collect(),
			self.body.typ.clone())
	}
}

#[derive(Clone, Debug)]
pub struct VarDef<'src> {
	pub binding: Ident<'src>,
	pub mutable: bool,
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>
}
impl<'src> VarDef<'src> {
	pub fn get_type(&self) -> &Type<'src> {
		&self.body.typ
	}
}

#[derive(Clone, Debug)]
pub struct Assign<'src> {
	pub lhs: ExprMeta<'src>,
	pub rhs: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub struct Deref<'src> {
	pub r: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub enum Expr<'src> {
	Nil(SrcPos<'src>),
	NumLit(&'src str, SrcPos<'src>),
	StrLit(borrow::Cow<'src, str>, SrcPos<'src>),
	Bool(bool, SrcPos<'src>),
	Binding(Path<'src>),
	Call(Call<'src>),
	Block(Block<'src>),
	If(If<'src>),
	Lambda(Lambda<'src>),
	VarDef(VarDef<'src>),
	Assign(Assign<'src>),
	Symbol(Ident<'src>),
	Deref(Deref<'src>),
}
impl<'src> Expr<'src> {
	pub fn is_var_def(&self) -> bool {
		if let &Expr::VarDef(_) = self { true } else { false }
	}

	fn pos(&self) -> &SrcPos<'src> {
		match *self {
			Expr::Nil(ref p)
			| Expr::NumLit(_, ref p)
			| Expr::StrLit(_, ref p)
			| Expr::Bool(_, ref p)
				=> p,
			Expr::Binding(ref path) => &path.pos,
			Expr::Call(ref call) => &call.pos,
			Expr::Block(ref block) => &block.pos,
			Expr::If(ref cond) => &cond.pos,
			Expr::Lambda(ref l) => &l.pos,
			Expr::VarDef(ref def) => &def.pos,
			Expr::Assign(ref a) => &a.pos,
			Expr::Symbol(ref s) => &s.pos,
			Expr::Deref(ref deref) => &deref.pos,
		}
	}

	fn as_binding(&self) -> Option<&Path<'src>> {
		match *self {
			Expr::Binding(ref path) => Some(path),
			_ => None,
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Clone, Debug)]
pub struct ExprMeta<'src> {
	pub val: Box<Expr<'src>>,
	pub typ: Type<'src>,
	pub ty_ascription: Option<(Type<'src>, SrcPos<'src>)>,
}
impl<'src> ExprMeta<'src> {
	pub fn new(value: Expr<'src>) -> Self {
		ExprMeta{ val: Box::new(value), typ: Type::Unknown, ty_ascription: None }
	}

	pub fn new_type_ascripted(value: Expr<'src>, typ: Type<'src>, pos: SrcPos<'src>) -> Self {
		ExprMeta{ val: Box::new(value), typ: Type::Unknown, ty_ascription: Some((typ, pos)) }
	}

	pub fn pos(&self) -> &SrcPos<'src> {
		self.ty_ascription.as_ref().map(|&(_, ref pos)| pos).unwrap_or(self.val.pos())
	}
}

#[derive(Clone, Debug)]
pub struct AST<'src> {
	pub uses: Vec<Use<'src>>,
	pub const_defs: HashMap<Ident<'src>, ConstDef<'src>>,
	pub extern_funcs: HashMap<Ident<'src>, Type<'src>>
}
