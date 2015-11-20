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

// TODO: Verify that all types are known

use std::collections::HashMap;
use std::mem::replace;
use lib::error;
use lib::ScopeStack;
use lib::front::ast::*;

#[derive(Debug)]
enum Usage {
	Used,
	Unused,
}
impl Usage {
	fn is_used(&self) -> bool {
		match *self {
			Usage::Used => true,
			_ => false
		}
	}
	fn is_unused(&self) -> bool {
		! self.is_used()
	}
}

struct Cleaner<'src> {
	const_defs: ScopeStack<Ident<'src>, Option<(ConstDef<'src>, Usage)>>,
}
impl<'src> Cleaner<'src> {
	fn new() -> Cleaner<'src> {
		Cleaner {
			const_defs: ScopeStack::new()
		}
	}

	fn clean_path(&mut self, path: &Path<'src>) {
		if let Some((id, height)) = path.as_ident()
			.and_then(|id| self.const_defs.get_height(id).map(|height| (id, height)))
		{
			let maybe_def = replace(
				self.const_defs.get_at_height_mut(id, height).unwrap(),
				None);

			if let Some((mut def, mut usage)) = maybe_def {
				if usage.is_unused() {
					usage = Usage::Used;

					self.clean_const_def(&mut def);
				}

				self.const_defs.update(id, Some((def, usage)));
			}
		}
	}

	fn clean_call(&mut self, call: &mut Call<'src>) {
		self.clean_expr(&mut call.proced);

		for arg in &mut call.args {
			self.clean_expr(arg);
		}
	}

	fn clean_block(&mut self, block: &mut Block<'src>) {
		self.const_defs.push(
			replace(&mut block.const_defs, HashMap::new())
				.into_iter()
				.map(|(k, def)| (k, Some((def, Usage::Unused))))
				.collect());

		for expr in &mut block.exprs {
			self.clean_expr(expr);
		}

		block.const_defs = self.const_defs.pop()
			.expect("ICE: clean_block: ScopeStack was empty when replacing Block const defs")
			.into_iter()
			.filter_map(|(key, maybe_def)|
				match maybe_def.expect("ICE: clean_block: None when unmapping block const def") {
					(def, Usage::Used) => Some((key, def)),
					(def, Usage::Unused) => {
						def.pos.warn(format!("Unused constant `{}`", key));
						None
					},
				})
			.collect();
	}

	fn clean_if(&mut self, cond: &mut If<'src>) {
		for expr in &mut [&mut cond.predicate, &mut cond.consequent, &mut cond.alternative] {
			self.clean_expr(expr);
		}
	}

	fn clean_lambda(&mut self, lambda: &mut Lambda<'src>) {
		self.clean_expr(&mut lambda.body);
	}

	fn clean_var_def(&mut self, def: &mut VarDef<'src>) {
		self.clean_expr(&mut def.body);
	}

	fn clean_assign(&mut self, assign: &mut Assign<'src>) {
		self.clean_expr(&mut assign.rhs);
	}

	fn clean_expr(&mut self, expr: &mut Expr<'src>) {
		match *expr {
			Expr::Binding(ref bnd) => self.clean_path(&bnd.path),
			Expr::Call(ref mut call) => self.clean_call(call),
			Expr::Block(ref mut block) => self.clean_block(block),
			Expr::If(ref mut cond) => self.clean_if(cond),
			Expr::Lambda(ref mut lambda) => self.clean_lambda(lambda),
			Expr::VarDef(ref mut def) => self.clean_var_def(def),
			Expr::Assign(ref mut assign) => self.clean_assign(assign),
			Expr::TypeAscript(ref mut ascr) => self.clean_expr(&mut ascr.expr),
			_ => (),
		}
	}

	fn clean_const_def(&mut self, def: &mut ConstDef<'src>) {
		self.clean_expr(&mut def.body)
	}
}

pub fn clean_ast(ast: &mut AST) {
	let mut cleaner = Cleaner::new();

	cleaner.const_defs.push(
		replace(&mut ast.const_defs, HashMap::new())
			.into_iter()
			.map(|(k, def)| (k, Some((def, Usage::Unused))))
			.collect());

	let main = replace(
		cleaner.const_defs.get_mut("main")
			.unwrap_or_else(|| error("No `main` procedure found")),
		None);

	let (mut main_def, mut main_usage) = main.unwrap();

	main_usage = Usage::Used;

	cleaner.clean_const_def(&mut main_def);

	cleaner.const_defs.update("main", Some((main_def, main_usage)));

	ast.const_defs = cleaner.const_defs.pop()
		.expect("ICE: clean_ast: ScopeStack was empty when replacing AST const defs")
		.into_iter()
		.filter_map(|(key, maybe_def)|
			match maybe_def.expect(
				&format!("ICE: clean_ast: `{}` was None when unmapping AST const def", key))
			{
				(def, Usage::Used) => Some((key, def)),
				(def, Usage::Unused) => {
					def.pos.warn(format!("Unused constant `{}`", key));
					None
				},
			})
		.collect();
}
