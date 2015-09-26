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

use lib::front::SrcPos;
use lib::ScopeStack;
use lib::front::parse::*;

type ConstDefs<'a> = ScopeStack<&'a str, Option<(ConstDef<'a>, Used)>>;

#[derive(Debug)]
enum Used {
	Yes,
	No,
}
impl Used {
	fn is_yes(&self) -> bool { match *self { Used::Yes => true, _ => false } }
	fn is_no(&self) -> bool { !self.is_yes() }
}

impl<'a> Path<'a> {
	fn remove_unused_consts(&self, const_defs: &mut ConstDefs) {
		if let Some(ident) = self.ident() {
			if let Some(height) = const_defs.get_height(ident) {
				if const_defs.get_at_height(ident, height).unwrap().is_some() {
					const_defs.do_for_item_at_height(ident, height, |const_defs, def|
						if def.1.is_no() {
							def.1 = Used::Yes;
							def.0.remove_unused_consts(const_defs)
						}
					)
				}
			}
		} else {
			panic!("Path::remove_unused_consts: Not implemented for anything but simple idents")
		}
	}
}

impl<'a> SExpr<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		self.proced.remove_unused_consts(const_defs);

		for arg in &mut self.args {
			arg.remove_unused_consts(const_defs);
		}
	}
}

impl<'a> Block<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		let mut const_defs = const_defs.map_push_local(
			&mut self.const_defs,
			|it| it.map(|(key, def)| (key, Some((def, Used::No)))),
			|it| it.filter_map(|(key, maybe_def)| match maybe_def.unwrap() {
				(def, Used::Yes) => Some((key, def)),
				(def, Used::No) => {
					def.pos.warn(format!("Unused constant `{}`", key));
					None
				},
			}));

		for expr in &mut self.exprs {
			expr.remove_unused_consts(&mut const_defs);
		}
	}
}

impl<'a> Cond<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		for pred in self.iter_predicates_mut() {
			pred.remove_unused_consts(const_defs);
		}
		for conseq in self.iter_consequences_mut() {
			conseq.remove_unused_consts(const_defs);
		}
	}
}

impl<'a> Lambda<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		self.body.remove_unused_consts(const_defs);
	}
}

impl<'a> VarDef<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		self.body.remove_unused_consts(const_defs);
	}
}

impl<'a> Assign<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		self.rvalue.remove_unused_consts(const_defs);
	}
}

impl<'a> ExprMeta<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		match *self.val {
			Expr::Binding(ref path) => path.remove_unused_consts(const_defs),
			Expr::SExpr(ref mut sexpr) => sexpr.remove_unused_consts(const_defs),
			Expr::Block(ref mut block) => block.remove_unused_consts(const_defs),
			Expr::Cond(ref mut cond) => cond.remove_unused_consts(const_defs),
			Expr::Lambda(ref mut lambda) => lambda.remove_unused_consts(const_defs),
			Expr::VarDef(ref mut def) => def.remove_unused_consts(const_defs),
			Expr::Assign(ref mut assign) => assign.remove_unused_consts(const_defs),
			_ => (),
		}
	}
}

impl<'a> ConstDef<'a> {
	fn remove_unused_consts(&mut self, const_defs: &mut ConstDefs<'a>) {
		self.body.remove_unused_consts(const_defs)
	}
}

impl<'a> AST<'a> {
	pub fn remove_unused_consts(&mut self) {
		let mut const_defs = ConstDefs::new();

		// Push the module scope on top of the stack
		let mut const_defs = const_defs.map_push_local(
			&mut self.const_defs,
			|it| it.map(|(key, def)| (key, Some((def, Used::No)))),
			|it| it.filter_map(|(key, maybe_def)| match maybe_def.unwrap() {
				(def, Used::Yes) => Some((key, def)),
				(def, Used::No) => {
					def.pos.warn(format!("Unused constant `{}`", key));
					None
				},
			}));

		const_defs.do_for_item_at_height("main", 0, |const_defs, main| {
			main.1 = Used::Yes;
			main.0.remove_unused_consts(const_defs)
		});
	}
}
