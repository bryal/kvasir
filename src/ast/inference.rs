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

//! Infer types where explicit type signatures are not available

use super::{ AST, ExprMeta, Expr, Type, TypedBinding };

// TODO: Add some way to check whether something was inferred
// in order to loop while things are still happening

impl super::Cond {
	fn get_type(&self, binding_stack: &[TypedBinding]) -> Option<Type> {
		self.clauses.iter()
			.filter_map(|&(_, ref clause_expr)| clause_expr.get_type(binding_stack))
			.next()
	}

	fn infer_types(&mut self, coerce_to: Option<&Type>, binding_stack: &mut Vec<TypedBinding>) {
		let out_type = self.clauses.iter()
			.filter_map(|&(_, ref clause_expr)| clause_expr.coerce_type.as_ref())
			.next()
			.or(coerce_to)
			.map(|o| o.clone());

		for clause in &mut self.clauses {
			clause.0.infer_types(Some(&Type::Basic("bool".into())), binding_stack);
			clause.1.infer_types(out_type.as_ref(), binding_stack);
		}
	}
}

impl super::SExpr {
	fn get_type(&self, binding_stack: &[TypedBinding]) -> Option<Type> {
		self.func.get_type(binding_stack)
	}

	fn infer_types(&mut self, _: Option<&Type>, binding_stack: &mut Vec<TypedBinding>) {
		self.func.infer_types(None, binding_stack);

		if let Expr::Lambda(ref mut lambda) = *self.func.value {
			for (sexpr_arg, lambda_arg) in
				self.args.iter_mut().zip(lambda.arg_bindings.iter_mut())
			{
				sexpr_arg.infer_types(lambda_arg.type_sig.as_ref(), binding_stack);
				lambda_arg.type_sig = sexpr_arg.get_type(binding_stack);
			}
		} else {
			for arg in &mut self.args {
				arg.infer_types(None, binding_stack);
			}
		}

		self.func.infer_types(None, binding_stack);
	}
}

impl super::Lambda {
	fn get_type(&self, _: &[TypedBinding]) -> Option<Type> {
		// TODO: Fix this. Should be something like:
		// `Type::Construct(Type::Basic("Fn".into), vec![Type::Tuple(vec![ARG_TYPES]), BODY_TYPE])`
		None
	}

	fn infer_types(&mut self, coerce_to: Option<&Type>, binding_stack: &mut Vec<TypedBinding>) {
		binding_stack.extend(self.arg_bindings.iter().cloned());

		self.body.infer_types(coerce_to, binding_stack);

		let old_len = binding_stack.len() - self.arg_bindings.len();
		binding_stack.truncate(old_len);
	}
}

impl super::Block {
	fn get_type(&self, binding_stack: &[TypedBinding]) -> Option<Type> {
		self.exprs.last().and_then(|expr| expr.get_type(binding_stack))
	}

	fn infer_types(&mut self, coerce_to: Option<&Type>, binding_stack: &mut Vec<TypedBinding>) {
		let old_stack_len = binding_stack.len();

		let all_but_last = self.exprs.len() - 1;
		for expr in self.exprs[0..all_but_last].iter_mut() {
			expr.infer_types(Some(&Type::Nil), binding_stack);
		}

		self.exprs.last_mut().unwrap().infer_types(coerce_to, binding_stack);

		binding_stack.truncate(old_stack_len);
	}
}

impl super::Definition {
	fn infer_types(&mut self, binding_stack: &mut Vec<TypedBinding>) {
		// TODO: inferral of function signature
		binding_stack.extend(self.arg_bindings.iter().cloned());

		self.body.infer_types(None, binding_stack);

		let old_len = binding_stack.len() - self.arg_bindings.len();
		binding_stack.truncate(old_len);
	}
}

impl ExprMeta {
	fn get_type(&self, binding_stack: &[TypedBinding])-> Option<Type> {
		self.coerce_type.clone().or(match *self.value {
			Expr::Cond(ref cond) => cond.get_type(binding_stack),
			Expr::SExpr(ref sexpr) => sexpr.get_type(binding_stack),
			// TODO: `&str` should somehow be parameterised Construct, not just a string
			Expr::StrLit(_) => Some(Type::Basic("&'static str".into())),
			Expr::Lambda(ref lambda) => lambda.get_type(binding_stack),
			Expr::Block(ref block) => block.get_type(binding_stack),
			Expr::Definition(_) | Expr::Nil => Some(Type::Nil),
			Expr::Binding(ref bnd) => binding_stack.iter()
				.rev()
				.find(|tb| tb.ident == *bnd)
				.map(|tb| tb.type_sig.clone())
				.unwrap_or(None),

			Expr::NumLit(_) => None,
		})
	}

	fn infer_types_for_child(&mut self, binding_stack: &mut Vec<TypedBinding>) {
		match *self.value {
			Expr::Cond(ref mut cond) => cond.infer_types(self.coerce_type.as_ref(), binding_stack),
			Expr::SExpr(ref mut sexpr) =>
				sexpr.infer_types(self.coerce_type.as_ref(), binding_stack),
			Expr::Lambda(ref mut lambda) =>
				lambda.infer_types(self.coerce_type.as_ref(), binding_stack),
			Expr::Block(ref mut block) =>
				block.infer_types(self.coerce_type.as_ref(), binding_stack),
			Expr::Definition(ref mut def) => def.infer_types(binding_stack),
			Expr::Binding(ref bnd) => if let Some(stack_binding) = binding_stack.iter_mut()
				.rev()
				.find(|tb| tb.ident == *bnd)
			{
				if self.coerce_type.is_none() {
					self.coerce_type = stack_binding.type_sig.clone();
				} else if stack_binding.type_sig.is_none() {
					stack_binding.type_sig = self.coerce_type.clone();
				}
			},
			// Doesn't have children to infer types for
			Expr::NumLit(_) | Expr::StrLit(_) | Expr::Nil => (),
		}
	}

	pub fn infer_type_from_below(&mut self, binding_stack: &[TypedBinding]) -> bool {
		if let Some(ty) = self.get_type(binding_stack) {
			self.coerce_type = Some(ty);
			true
		} else {
			false
		}
	}

	// Infer types for self and for children
	pub fn infer_types(&mut self, coerce_to: Option<&Type>, binding_stack: &mut Vec<TypedBinding>) {
		if self.coerce_type.is_some() {
			// We have a type, infer types for children,
			// resorting to coercing to our type if necessary
			self.infer_types_for_child(binding_stack);
		} else {
			// We don't have a type, try to infer types for children from below
			self.infer_types_for_child(binding_stack);
			if self.infer_type_from_below(&binding_stack) {
				// We got a type from below, redo procedure with coerce type available for children
				// that can't get types from below
				self.infer_types(None, binding_stack);
			} else {
				if let Some(coerce_type) = coerce_to {
					// We didn't get a type from below, resort to using type of parent to coerce to
					self.coerce_type = Some(coerce_type.clone());
					self.infer_types(None, binding_stack);
				}
			}
		}
	}
}

impl AST {
	pub fn infer_types(&mut self) {
		let mut binding_stack = Vec::with_capacity(10);
		for expr in &mut self.exprs {
			expr.infer_types(None, &mut binding_stack);
		}
	}
}