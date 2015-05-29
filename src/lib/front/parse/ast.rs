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

use std::collections::HashMap;
use std::iter::FromIterator;
use std::convert::Into;
use lib;
use lib::{ Path, Use, Type, TypedBinding };

#[derive(Clone, Debug)]
enum MacroPattern {
	Ident(String),
	Pattern(Vec<MacroPattern>),
}

#[derive(Clone, Debug)]
pub struct MacroRules {
	literal_idents: Vec<String>,
	rules: Vec<(Vec<MacroPattern>, ExprMeta)>,
}

#[derive(Clone, Debug)]
pub struct SExpr {
	pub func: ExprMeta,
	pub args: Vec<ExprMeta>,
}
impl Into<lib::SExpr> for SExpr {
	fn into(self) -> lib::SExpr {
		lib::SExpr{
			func: self.func.into(),
			args: self.args.into_iter().map(|a| a.into()).collect()
		}
	}
}

#[derive(Clone, Debug)]
pub struct Block {
	pub macro_defs: HashMap<String, MacroRules>,
	pub uses: Vec<Use>,
	pub const_defs: HashMap<String, ExprMeta>,
	pub exprs: Vec<ExprMeta>,
}
impl Into<lib::Block> for Block {
	fn into(self) -> lib::Block {
		lib::Block{
			uses: self.uses,
			const_defs: HashMap::from_iter(self.const_defs.into_iter().map(|(k, v)| (k, v.into()))),
			exprs: self.exprs.map_in_place(|e| e.into())
		}
	}
}

#[derive(Clone, Debug)]
pub struct Cond {
	pub clauses: Vec<(ExprMeta, ExprMeta)>,
	pub else_clause: Option<ExprMeta>
}
impl Into<lib::Cond> for Cond {
	fn into(self) -> lib::Cond {
		lib::Cond{
			clauses: self.clauses.map_in_place(|(p, c)| (p.into(), c.into())),
			else_clause: self.else_clause.map(|c| c.into()),
		}
	}
}

#[derive(Clone, Debug)]
pub struct Lambda {
	pub arg_bindings: Vec<TypedBinding>,
	pub body: ExprMeta
}
impl Into<lib::Lambda> for Lambda {
	fn into(self) -> lib::Lambda {
		lib::Lambda{ arg_bindings: self.arg_bindings, body: self.body.into() }
	}
}

#[derive(Clone, Debug)]
pub struct VarDef {
	pub binding: TypedBinding,
	pub mutable: bool,
	pub body: ExprMeta,
}
impl Into<lib::VarDef> for VarDef {
	fn into(self) -> lib::VarDef {
		lib::VarDef{ binding: self.binding, mutable: self.mutable, body: self.body.into() }
	}
}

#[derive(Clone, Debug)]
pub struct Assign {
	pub lvalue: TypedBinding,
	pub rvalue: ExprMeta,
}
impl Into<lib::Assign> for Assign {
	fn into(self) -> lib::Assign {
		lib::Assign{ lvalue: self.lvalue, rvalue: self.rvalue.into() }
	}
}

#[derive(Clone, Debug)]
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
	VarDef(VarDef),
	Assign(Assign)
}
impl Into<lib::Expr> for Expr {
	fn into(self) -> lib::Expr {
		match self {
			Expr::Nil => lib::Expr::Nil,
			Expr::NumLit(n) => lib::Expr::NumLit(n),
			Expr::StrLit(s) => lib::Expr::StrLit(s),
			Expr::Bool(b) => lib::Expr::Bool(b),
			Expr::Binding(p) => lib::Expr::Binding(p),
			Expr::SExpr(e) => lib::Expr::SExpr(e.into()),
			Expr::Block(b) => lib::Expr::Block(b.into()),
			Expr::Cond(c) => lib::Expr::Cond(c.into()),
			Expr::Lambda(l) => lib::Expr::Lambda(l.into()),
			Expr::VarDef(v) => lib::Expr::VarDef(v.into()),
			Expr::Assign(a) => lib::Expr::Assign(a.into())
		}
	}
}

#[derive(Clone, Debug)]
pub struct ExprMeta {
	pub value: Box<Expr>,
	pub type_: Type
}
impl ExprMeta {
	pub fn new(value: Expr, ty: Type) -> Self { ExprMeta{ value: Box::new(value), type_: ty } }
	pub fn new_nil() -> ExprMeta { ExprMeta::new(Expr::Nil, Type::new_nil()) }
}
impl Into<lib::ExprMeta> for ExprMeta {
	fn into(self) -> lib::ExprMeta { lib::ExprMeta::new((*self.value).into(), self.type_) }
}

pub struct AST {
	pub macro_defs: HashMap<String, MacroRules>,
	pub uses: Vec<Use>,
	pub const_defs: HashMap<String, ExprMeta>,
}
impl Into<lib::AST> for AST {
	fn into(self) -> lib::AST {
		lib::AST{
			uses: self.uses,
			const_defs: HashMap::from_iter(self.const_defs.into_iter().map(|(k, v)| (k, v.into())))
		}
	}
}
