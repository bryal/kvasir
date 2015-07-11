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
pub struct SExpr {
	pub func: Expr,
	pub args: Vec<Expr>,
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
	pub const_defs: HashMap<String, Expr>,
	pub exprs: Vec<Expr>,
}
impl Into<lib::Block> for Block {
	fn into(self) -> lib::Block {
		lib::Block{
			uses: self.uses,
			const_defs: HashMap::from_iter(self.const_defs.into_iter().map(|(k, v)| (k, v.into()))),
			exprs: self.exprs.into_iter().map(|e| e.into()).collect()
		}
	}
}

#[derive(Clone, Debug)]
pub struct Cond {
	pub clauses: Vec<(Expr, Expr)>,
	pub else_clause: Option<Expr>
}
impl Into<lib::Cond> for Cond {
	fn into(self) -> lib::Cond {
		lib::Cond{
			clauses: self.clauses.into_iter().map(|(p, c)| (p.into(), c.into())).collect(),
			else_clause: self.else_clause.map(|c| c.into()),
		}
	}
}

#[derive(Clone, Debug)]
pub struct Lambda {
	pub arg_bindings: Vec<TypedBinding>,
	pub body: Expr
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
	pub body: Expr,
}
impl Into<lib::VarDef> for VarDef {
	fn into(self) -> lib::VarDef {
		lib::VarDef{ binding: self.binding, mutable: self.mutable, body: self.body.into() }
	}
}

#[derive(Clone, Debug)]
pub struct Assign {
	pub lvalue: TypedBinding,
	pub rvalue: Expr,
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
	TypeAscr(Type, Box<Expr>),
	SExpr(Box<SExpr>),
	Block(Box<Block>),
	Cond(Box<Cond>),
	Lambda(Box<Lambda>),
	VarDef(Box<VarDef>),
	Assign(Box<Assign>),
	Symbol(String),
	List(Vec<Expr>)
}
impl Into<lib::ExprMeta> for Expr {
	fn into(self) -> lib::ExprMeta {
		let expr = match self {
			Expr::Nil => lib::Expr::Nil,
			Expr::NumLit(n) => lib::Expr::NumLit(n),
			Expr::StrLit(s) => lib::Expr::StrLit(s),
			Expr::Bool(b) => lib::Expr::Bool(b),
			Expr::Binding(p) => lib::Expr::Binding(p),
			Expr::TypeAscr(ty, box e) => return lib::ExprMeta{ type_: ty, ..e.into() },
			Expr::SExpr(box e) => lib::Expr::SExpr(e.into()),
			Expr::Block(box b) => lib::Expr::Block(b.into()),
			Expr::Cond(box c) => lib::Expr::Cond(c.into()),
			Expr::Lambda(box l) => lib::Expr::Lambda(l.into()),
			Expr::VarDef(box v) => lib::Expr::VarDef(v.into()),
			Expr::Assign(box a) => lib::Expr::Assign(a.into()),
			Expr::Symbol(s) => lib::Expr::Symbol(s),
			Expr::List(l) => lib::Expr::List(l.into_iter().map(|e| e.into()).collect()),
		};

		lib::ExprMeta::new(expr, Type::Inferred)
	}
}

#[derive(Debug)]
pub struct AST {
	pub block: Block,
}
impl Into<lib::AST> for AST {
	fn into(self) -> lib::AST {
		lib::AST{
			uses: self.block.uses,
			const_defs: HashMap::from_iter(
				self.block.const_defs.into_iter().map(|(k, v)| (k, v.into())))
		}
	}
}
