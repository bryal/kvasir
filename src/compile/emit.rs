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

//! Emit the AST in some format
//!
//! Which formats should be supported:
//! 	* Rust source code ☑
//! 	* Rust AST ☐
//! 	* LLVM something ☐

use ast::*;
use std::fmt::Write;

pub trait ToRustSrc {
	fn to_rust_src(&self) -> String;
}

impl ToRustSrc for Type {
	fn to_rust_src(&self) -> String {
		match *self {
			Type::Basic(ref ty) => ty.clone(),
			Type::Construct(ref con, ref args) => format!(
				"{}<{}>",
				con,
				args.iter().fold(String::new(), |acc, ty| format!("{}{},", acc, ty.to_rust_src()))),
			Type::Tuple(ref types) => format!(
				"({})",
				types.iter().fold(String::new(), |acc, ty| format!("{}{},", acc, ty.to_rust_src())))
		}
	}
}

impl ToRustSrc for TypedBinding {
	fn to_rust_src(&self) -> String {
		format!("{}{}",
			self.ident,
			self.type_sig.as_ref().map(|ty| format!(": {}", ty.to_rust_src())).unwrap_or("".into())
		)
	}
}

impl ToRustSrc for Use {
	fn to_rust_src(&self) -> String {
		self.paths.iter()
			.fold(String::new(), |acc, ident| format!("{}use {};", acc, ident.to_rust_src()))
	}
}

impl ToRustSrc for FnDef {
	fn to_rust_src(&self) -> String {
		format!("fn {}({}) -> {} {{ {} }}",
			self.binding.ident,
			self.arg_bindings.first()
				.map(|first| self.arg_bindings[1..].iter()
					.fold(first.to_rust_src(), |acc, bnd|
						format!("{}, {}", acc, bnd.to_rust_src())))
				.unwrap_or("".into()),
			self.body.coerce_type.as_ref()
				.expect(&format!("FnDef::to_rust_src: function body of `{}` has no type",
					self.binding.ident))
				.to_rust_src(),
			self.body.to_rust_src()
		)
	}
}

impl ToRustSrc for ConstDef {
	fn to_rust_src(&self) -> String {
		format!("const {}: {} = {};",
			self.binding.ident,
			self.binding.type_sig.as_ref()
				.expect(&format!("ConstDef::to_rust_src: binding `{}` has no type",
					self.binding.ident))
				.to_rust_src(),
			self.body.to_rust_src()
		)
	}
}

impl ToRustSrc for ItemMeta {
	fn to_rust_src(&self) -> String {
		match *self.item {
			Item::Use(ref u) => u.to_rust_src(),
			Item::FnDef(ref def) => def.to_rust_src(),
			Item::ConstDef(ref def) => def.to_rust_src(),
		}
	}
}

impl ToRustSrc for Path {
	fn to_rust_src(&self) -> String {
		format!(
			"{}{}{}",
			if self.is_absolute() { "::" } else { "" },
			self.parts()[0],
			self.parts()[1..].iter().fold(String::new(), |acc, s| format!("{}::{}", acc, s)))
	}
}

impl ToRustSrc for SExpr {
	fn to_rust_src(&self) -> String {
		format!("{}({})",
			self.func.to_rust_src(),
			self.args.first()
				.map(|first| self.args[1..].iter()
					.fold(first.to_rust_src(), |acc, bnd|
						format!("{}, {}", acc, bnd.to_rust_src())))
				.unwrap_or("".into()),
		)
	}
}

impl ToRustSrc for Block {
	fn to_rust_src(&self) -> String {
		self.exprs.first()
			.map(|first| self.exprs[1..].iter()
				.fold(format!("{{ {}", first.to_rust_src()), |acc, expr|
					format!("{}; {}", acc, expr.to_rust_src())) + "}")
			.unwrap_or("{ }".into())
	}
}

impl ToRustSrc for Cond {
	fn to_rust_src(&self) -> String {
		format!("if {} {{ {} }}{}{}",
			self.clauses[0].0.to_rust_src(),
			self.clauses[0].1.to_rust_src(),
			self.clauses.iter().fold(String::new(), |acc, &(ref cond, ref conseq)|
				format!("{} else if {} {{ {} }}", acc, cond.to_rust_src(), conseq.to_rust_src())),
			self.else_clause.as_ref().map(|conseq| format!(" else {{ {} }}", conseq.to_rust_src()))
				.unwrap_or("".into()),
		)
	}
}

impl ToRustSrc for Lambda {
	fn to_rust_src(&self) -> String {
		format!("|{}| {} {{ {} }}",
			self.arg_bindings.first()
				.map(|first| self.arg_bindings[1..].iter()
					.fold(first.to_rust_src(), |acc, bnd|
						format!("{}, {}", acc, bnd.to_rust_src())))
				.unwrap_or("".into()),
			self.body.coerce_type.as_ref().map(|body| format!("-> {}", body.to_rust_src()))
				.unwrap_or("".into()),
			self.body.to_rust_src()
		)
	}
}

impl ToRustSrc for ExprMeta {
	fn to_rust_src(&self) -> String {
		let as_type = self.coerce_type.as_ref().map(|ty| format!(" as {}", ty.to_rust_src()));

		match *self.value {
			Expr::Cond(ref cond) => cond.to_rust_src(),
			Expr::SExpr(ref sexpr) => sexpr.to_rust_src(),
			Expr::NumLit(ref s) => as_type
				.map(|as_type| format!("({}{})", s.clone(), as_type))
				.unwrap_or(s.clone()),
			Expr::Binding(ref ident) => ident.to_rust_src(),
			Expr::StrLit(ref s) => s.clone(),
			Expr::Lambda(ref λ) => λ.to_rust_src(),
			Expr::Block(ref block) => block.to_rust_src(),
			Expr::Nil => "()".into(),
		}
	}
}

impl ToRustSrc for AST {
	fn to_rust_src(&self) -> String {
		let mut src = String::with_capacity(500);

		for item in &self.items {
			writeln!(src, "{}", item.to_rust_src()).unwrap();
		}

		src
	}
}

pub fn generate_rust_src(ast: &AST) -> String {
	ast.to_rust_src()
}
