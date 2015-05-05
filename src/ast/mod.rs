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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedBinding {
	pub ident: String,
	pub type_sig: Option<Type>,
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
pub struct FnDef {
	pub binding: TypedBinding,
	pub arg_bindings: Vec<TypedBinding>,
	pub body: ExprMeta,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
	pub binding: TypedBinding,
	pub body: ExprMeta,
}

#[derive(Debug, Clone)]
pub enum Item {
	Use(Use),
	FnDef(FnDef),
	ConstDef(ConstDef),
}

#[derive(Debug, Clone)]
pub struct ItemMeta {
	pub item: Box<Item>,
	// pub attributes: Vec<Attribute>
}

#[derive(Debug, Clone)]
pub struct SExpr {
	pub func: ExprMeta,
	pub args: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
pub struct Block {
	pub items: Vec<ItemMeta>,
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
pub enum Expr {
	NumLit(String),
	StrLit(String),
	Binding(Path),
	SExpr(SExpr),
	Block(Block),
	Cond(Cond),
	Lambda(Lambda),
	Nil,
}

/// An expression with additional attributes such as type information
#[derive(Debug, Clone)]
pub struct ExprMeta {
	pub value: Box<Expr>,
	pub coerce_type: Option<Type>
}
impl ExprMeta {
	fn new(value: Expr, coerce_type: Option<Type>) -> ExprMeta {
		ExprMeta{ value: Box::new(value), coerce_type: coerce_type }
	}
}

/// Nodes are found in blocks. E.g. a function body with multiple things in it is a block.
/// Therein can be `use` items, expressions, and more.
pub enum Component {
	Item(ItemMeta),
	Expr(ExprMeta),
}

#[derive(Debug, Clone)]
pub struct AST {
	pub items: Vec<ItemMeta>,
}
