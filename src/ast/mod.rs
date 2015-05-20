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

mod parse;
mod inference;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
	Basic(String),
	Construct(String, Vec<Type>),
	Tuple(Vec<Type>),
}
impl Type {
	fn nil() -> Type {
		Type::Tuple(vec![])
	}

	fn basic<T: Into<String>>(ts: T) -> Type {
		Type::Basic(ts.into())
	}

	fn construct<T: Into<String>>(constructor: T, args: Vec<Type>) -> Type {
		Type::Construct(constructor.into(), args)
	}

	fn fn_sig(arg_tys: Vec<Type>, return_ty: Type) -> Type {
		arg_tys.push(return_ty);
		Type::Construct("→".into(), arg_tys)
	}

	fn bool() -> Type {
		Type::Basic("bool".into())
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedBinding {
	pub ident: String,
	pub type_sig: Option<Type>,
}
impl TypedBinding {
	fn has_type(&self) -> bool {
		self.type_sig.is_some()
	}
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Debug, Clone)]
pub struct Path {
	parts: Vec<String>,
	is_absolute: bool,
}
impl Path {
	fn new(parts: Vec<String>, is_absolute: bool) -> Path {
		Path{ parts: parts, is_absolute: is_absolute }
	}

	pub fn is_absolute(&self) -> bool { self.is_absolute }

	pub fn parts(&self) -> &[String] { &self.parts }

	pub fn to_str(&self) -> String {
		format!(
			"{}{}{}",
			if self.is_absolute() { "/" } else { "" },
			self.parts[0],
			self.parts[1..].iter().fold(String::new(), |acc, p| acc + "/" + p))
	}
}
impl PartialEq<str> for Path {
	fn eq(&self, rhs: &str) -> bool {
		self.to_str() == rhs
	}
}

#[derive(Debug, Clone)]
pub struct Use {
	pub paths: Vec<Path>,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
	pub binding: TypedBinding,
	pub body: ExprMeta,
}

pub struct Items {
	pub uses: Vec<Use>,
	pub constant_defs: Vec<ConstDef>,
	// pub attributes: Vec<Attribute>
}

#[derive(Debug, Clone)]
pub struct SExpr {
	pub func: ExprMeta,
	pub args: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
pub struct Block {
	pub uses: Vec<Use>,
	pub const_defs: Vec<ConstDef>,
	pub exprs: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
pub struct Cond {
	pub clauses: Vec<(ExprMeta, ExprMeta)>,
	pub else_clause: Option<ExprMeta>
}

#[derive(Debug, Clone)]
pub struct Lambda {
	pub arg_bindings: Vec<TypedBinding>,
	pub body: ExprMeta
}

#[derive(Debug, Clone)]
pub struct Assignment {
	pub lvalue: TypedBinding,
	pub rvalue: ExprMeta,
}

#[derive(Debug, Clone)]
pub enum Expr {
	Nil,
	NumLit(String),
	StrLit(String),
	Bool(bool),
	Binding(Path),
	SExpr(SExpr),
	Block(Block),
	Cond(Cond),
	Lambda(Lambda),
	VarDecl(TypedBinding),
	Assignment(Assignment)
}
impl Expr {
	fn is_var_def(&self) -> bool {
		if let Expr::VarDef(_) = *self {
			true
		} else {
			false
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Debug, Clone)]
pub struct ExprMeta {
	pub value: Box<Expr>,
	pub type_: Option<Type>
}
impl ExprMeta {
	fn new(value: Expr, ty: Option<Type>) -> ExprMeta {
		ExprMeta{ value: Box::new(value), type_sig: ty }
	}

	fn new_true() -> ExprMeta {
		ExprMeta::new(Expr::Bool(true), Some(Type::bool()))
	}

	fn new_false() -> ExprMeta {
		ExprMeta::new(Expr::Bool(false), Some(Type::bool()))
	}

	fn nil() -> ExprMeta {
		ExprMeta::new(Expr::Nil, Some(Type::nil()))
	}

	fn expr(&mut self) -> &mut Expr {
		&mut self.value
	}
}

pub enum Item {
	Use(Use),
	ConstDef(ConstDef),
	Expr(ExprMeta),
}

#[derive(Debug, Clone)]
pub struct AST {
	pub items: Vec<Item>,
}
