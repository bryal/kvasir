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

#[derive(Debug, Clone)]
pub enum Type {
	Nil,
	Basic(String),
	Construct(String, Vec<Type>),
}

#[derive(Debug, Clone)]
pub struct TypedBinding {
	pub ident: String,
	pub type_sig: Option<Type>,
}

/// e.g. Path(fs, Path(File, Name(create))) == fs::File::create
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ident {
	Name(String),
	Path(String, Box<Ident>),
}
impl PartialEq<String> for Ident {
	fn eq(&self, s: &String) -> bool {
		&::compile::emit::ToRustSrc::to_rust_src(self) == s
	}
}

#[derive(Debug, Clone)]
pub struct Use {
	pub paths: Vec<Ident>,
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
	Binding(Ident),
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
	pub exprs: Vec<ExprMeta>,
}
