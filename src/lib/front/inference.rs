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

// TODO: Check for mutual recursion when infering types. Maybe list of function call ancestry.
//       Like: foo calling bar calling baz calling foo => ERROR
// TODO: Consider redisigning this module. Maybe have an Inferer that takes expressions instead
//       of implementing inference for each expression type.
// TODO: Infer types for incomplete function sig. E.g. (:<→ u32 _> inc) => (:<→ u32 u32> inc)
// TODO: Almost all `infer_types` takes const map + var stack + caller stack.
//       Maybe encapsulate this using some kind of State object
// TODO: Add field on things to keep track of whether inference has happened

use std::borrow::Cow;

use lib::front::parse::*;
use lib::collections::ScopeStack;
use super::core_lib::CORE_CONSTS_TYPES;

type ConstDefs<'src> = ScopeStack<&'src str, Option<ConstDef<'src>>>;

fn get_var_type<'src, 't>(var_types: &'t [TypedBinding<'src>], ident: &str) -> Option<&'t Type<'src>> {
	var_types.iter().rev().find(|tb| tb.ident == ident).map(|tb| &tb.typ)
}
fn get_var_type_mut<'src, 't>(var_types: &'t mut Vec<TypedBinding<'src>>, bnd: &str)
	-> Option<&'t mut Type<'src>>
{
	var_types.iter_mut().rev().find(|tb| tb.ident == bnd).map(|tb| &mut tb.typ)
}

impl<'src> Type<'src> {
	/// Recursively infer all Inferred to the `to` type.
	/// If types are different and not inferrable, panic.
	fn infer_to(&self, to: &Type<'src>) -> Self {
		match (self, to) {
			(_, _) if self == to => self.clone(),
			(&Type::Unknown, _) => to.clone(),
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				Type::Construct(
					s1.clone(),
					as1.iter()
						.zip(as2.iter())
						.map(|(a1, a2)| a1.infer_to(a2)).collect()),
			_ => panic!("Type::infer_to: Can't infer {:?} to {:?}", self, to),
		}
	}

	/// Recursively infer all Inferred by the `by` type. If types are different and not inferrable,
	/// just ignore and return self
	fn infer_by(&self, by: &Self) -> Self {
		match (self, by) {
			(_, _) if self == by => self.clone(),
			(&Type::Unknown, _) => by.clone(),
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				Type::Construct(
					s1.clone(),
					as1.iter()
						.zip(as2.iter())
						.map(|(a1, a2)| a1.infer_by(a2)).collect()),
			(_, _) => self.clone(),
		}
	}

	fn specialize_to(&self, constraint: &Self) -> Self {
		match (self, constraint) {
			(_, _) if self == constraint => self.clone(),
			(&Type::Unknown, _) => panic!("Type::specialize_to: Can't specialize unknown type"),
			(_, &Type::Unknown) => panic!("Type::specialize_to: Constraint is unknown"),
			(&Type::Basic(_), &Type::Basic(_)) if self == constraint => self.clone(),
			(&Type::Construct(ref s1, ref gens), &Type::Construct(ref s2, ref specs)) =>
				Type::Construct(s1.clone(), constrain_related_types(gens, specs)),
			(&Type::Poly(_), _) => constraint.clone(),
			(_, &Type::Poly(_)) => self.clone(),
			_ => panic!("Type::specialize_to: Can't specialize {:?} into {:?}", self, constraint),
		}
	}

	fn add_constraint(&self, constraint: &Self) -> Self {
		match (self, constraint) {
			(_, _) if self == constraint => self.clone(),
			(&Type::Unknown, _) => constraint.clone(),
			(_, &Type::Unknown) => self.clone(),
			(&Type::Basic(_), &Type::Basic(_)) if self == constraint => self.clone(),
			(&Type::Construct(ref s1, ref gens), &Type::Construct(ref s2, ref specs)) =>
				Type::Construct(s1.clone(), constrain_related_types(gens, specs)),
			(&Type::Poly(_), _) => constraint.clone(),
			(_, &Type::Poly(_)) => self.clone(),
			_ => panic!("Type::add_constraint: Can't specialize {:?} into {:?}", self, constraint),
		}
	}
}

fn constrain_related_types<'src>(generals: &[Type<'src>], criteria: &[Type<'src>])
	-> Vec<Type<'src>>
{
	if generals.len() != criteria.len() {
		panic!("specialize_related: Slices differ in length");
	}

	let mut constraining: Vec<_> = generals.into();

	for (i, criterium) in criteria.iter().enumerate() {
		if constraining[i].is_poly() {
			let current_specializing = constraining[i].clone();

			let constrained = current_specializing.add_constraint(criterium);

			let same_type_args: Vec<_> = constraining[i..].iter_mut()
				.filter(|ty| *ty == &current_specializing)
				.collect();

			for same in same_type_args {
				*same = constrained.clone();
			}
		} else {
			constraining[i] = constraining[i].add_constraint(criterium);
		}
	}

	constraining
}

impl<'src> ConstDef<'src> {
	fn get_type(&self) -> &Type<'src> {
		&self.body.typ
	}

	fn infer_types(&mut self,
		expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		self.body.infer_types(expected_type, var_types, const_defs)
	}
}

impl<'src> Path<'src> {
	fn get_type(&self,
		constraint: &Type<'src>,
		var_types: &[TypedBinding<'src>],
		const_defs: &ConstDefs<'src>
	) -> Type<'src> {
		let general = if let Some(ident) = self.ident() {
			if let Some(ty) = CORE_CONSTS_TYPES.get(ident) {
				ty.clone()
			} else if let Some((def, _)) = const_defs.get(ident) {
				def.as_ref().map_or(Type::Unknown, |e| e.get_type().clone())
			} else if let Some(var_stack_ty) = get_var_type(var_types, ident) {
				var_stack_ty.clone()
			} else {
				panic!("Path::get_type: Unresolved path `{}`", ident)
			}
		} else {
			panic!("Path::get_type: Not implemented for anything but simple idents")
		};
		// Fill in the blanks. A known type can't be inferred to be an unknown type
		general.add_constraint(&constraint.infer_by(&general))
	}

	fn infer_types(&self,
		expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		if let Some(ident) = self.ident() {
			if CORE_CONSTS_TYPES.get(ident).is_some() {
				// Don't try to infer types for internal functions
				()
			} else if let Some(height) = const_defs.get_height(ident) {
				// Path is a constant
				if const_defs.get_at_height(ident, height).unwrap().is_some() {
					const_defs.do_for_item_at_height(ident, height, |const_defs, def|
						def.infer_types(&Type::Unknown, &mut Vec::new(), const_defs))
				}
			} else if expected_type.is_partially_known() {
				if let Some(stack_bnd_ty) = get_var_type_mut(var_types, ident) {
					// Path is a var
					*stack_bnd_ty = stack_bnd_ty.infer_by(expected_type)
						.add_constraint(expected_type);
				} else {
					panic!("Path::infer_types: Binding not on stack")
				}
			}
		} else {
			panic!("Path::infer_types: Not implemented for anything but simple idents")
		}
	}
}

/// Extract a function type signature in the form of <→ arg1 arg2 body> to (&[arg1, arg2], body)
fn extract_fn_sig<'src, 't>(sig: &'t Type<'src>) -> Option<(&'t [Type<'src>], &'t Type<'src>)> {
	match sig {
		&Type::Construct("proc", ref ts) => Some((ts.init(), ts.last().unwrap())),
		_ => None,
	}
}

impl<'src> SExpr<'src> {
	fn body_type(&self) -> &Type<'src> {
		extract_fn_sig(&self.proced.typ).expect("SExpr::body_type: Could not extract fn sig").1
	}

	fn infer_arg_types(&mut self,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		let inferreds = if self.proced.typ.is_unknown() {
			vec![Type::Unknown; self.args.len()]
		} else {
			vec![]
		};

		let expected_types = if self.proced.typ.is_partially_known() {
			extract_fn_sig(&self.proced.typ)
				.expect("SExpr::infer_arg_types: Could not extract fn sig")
				.0

		} else {
			inferreds.as_ref()
		};

		if self.args.len() != expected_types.len() {
			panic!("SExpr::infer_arg_types: Arity mismatch. Expected {}, found {}",
				expected_types.len(),
				self.args.len())
		}

		for (arg, expect_ty) in self.args.iter_mut().zip(expected_types) {
			arg.infer_types(expect_ty, var_types, const_defs);
		}
	}

	fn infer_types(&mut self,
		parent_expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		self.infer_arg_types(var_types, const_defs);

		let expected_fn_type = Type::new_proc(
			self.args.iter().map(|tb| tb.typ.clone()).collect(),
			parent_expected_type.clone());

		self.proced.infer_types(&expected_fn_type, var_types, const_defs);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if self.proced.typ.is_partially_known() {
			self.infer_arg_types(var_types, const_defs);
		}
	}
}

impl<'src> Block<'src> {
	fn get_type(&self) -> &Type<'src> {
		&self.exprs.last().expect("Block::get_type: No expressions in block").typ
	}

	fn infer_types(&mut self,
		parent_expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		if self.exprs.len() == 0 {
			return;
		}

		let mut const_defs = const_defs.map_push_local(
			&mut self.const_defs,
			|it| it.map(|(k, v)| (k, Some(v))),
			|it| it.map(|(k, v)| (k, v.unwrap())));

		let old_vars_len = var_types.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in self.exprs.init_mut() {
			match expr {
				&mut ExprMeta{ val: box Expr::VarDef(ref mut var_def), .. } => {
					var_def.infer_types(var_types, &mut const_defs);
					var_types.push(var_def.binding.clone());
				},
				_ => expr.infer_types(&Type::Unknown, var_types, &mut const_defs)
			}
		}

		if self.exprs.last_mut().unwrap().val.is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut()
				.unwrap()
				.infer_types(parent_expected_type, var_types, &mut const_defs);
		}

		let mut block_defined_vars = var_types.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in self.exprs.init_mut() {
			if let &mut ExprMeta{ val: box Expr::VarDef(ref mut var_def), .. } = expr {
				var_def.infer_types(var_types, &mut const_defs);

				var_types.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(&Type::Unknown, var_types, &mut const_defs);
			}
		}

		if self.exprs.last_mut().unwrap().val.is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut()
				.unwrap()
				.infer_types(parent_expected_type, var_types, &mut const_defs);
		}
	}
}

impl<'src> Cond<'src> {
	fn get_type<'t>(&'t self) -> &'t Type<'src> {
		match self.iter_consequences().map(|c| &c.typ).find(|ty| ty.is_partially_known()) {
			Some(found) => found,
			None => &self.iter_consequences().next().unwrap().typ
		}
	}

	fn infer_types(&mut self,
		expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		if expected_type.is_unknown() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::new_basic("bool"), var_types, const_defs);
			}
			for consequence in self.iter_consequences_mut() {
				if consequence.typ.is_partially_known() || {
					consequence.infer_types(&Type::Unknown, var_types, const_defs);
					consequence.typ.is_partially_known()
				} {
					found_type = Some(consequence.typ.clone());
					break;
				}
			}

			if let Some(ref expected_type) = found_type {
				self.infer_types(expected_type, var_types, const_defs)
			}
		} else {
			for &mut (ref mut predicate, ref mut consequence) in self.clauses.iter_mut() {
				predicate.infer_types(&Type::new_basic("bool"), var_types, const_defs);
				consequence.infer_types(expected_type, var_types, const_defs);
			}
			if let Some(ref mut else_clause) = self.else_clause {
				else_clause.infer_types(expected_type, var_types, const_defs);
			}
		}
	}
}

fn inferred_to_polymorphic(mut binds: Vec<TypedBinding>) -> Vec<TypedBinding> {
	for bind in &mut binds {
		if bind.typ.is_unknown() {
			bind.typ = Type::new_poly(format!("__Poly_{}", bind.ident));
		}
	}

	binds
}

impl<'src> Lambda<'src> {
	fn infer_arg_types(&mut self, constraints: &[Type<'src>]) {
		for (arg, constraint) in self.params.iter_mut().zip(constraints) {
			arg.typ = arg.typ.infer_to(constraint);
		}
	}

	fn get_type(&self) -> Type<'src> {
		Type::new_proc(
			self.params.iter().map(|tb| tb.typ.clone()).collect(),
			self.body.typ.clone())
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self,
		constraint: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		let body_constraint =
			if let Some((args_constraints, body_constraint)) = extract_fn_sig(constraint)
		{
			self.infer_arg_types(args_constraints);

			self.body.typ.infer_by(body_constraint).add_constraint(body_constraint)
		} else {
			self.body.typ.clone()
		};

		let (vars_len, args_len) = (var_types.len(), self.params.len());

		var_types.extend(inferred_to_polymorphic(self.params.clone()));

		self.body.infer_types(&body_constraint, var_types, const_defs);

		assert_eq!(var_types.len(), vars_len + args_len);

		for (arg, found) in self.params.iter_mut()
			.zip(var_types.drain(vars_len..))
			.map(|(arg, found)| (&mut arg.typ, found.typ))
		{
			let inferred = arg.infer_by(&found);
			if inferred == found {
				*arg = inferred;
			} else {
				panic!("Lambda::infer_types: Function signature doesn't match actual type");
			}
		}
	}
}

impl<'src> VarDef<'src> {
	fn infer_types(&mut self,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		self.body.infer_types(&self.binding.typ, var_types, const_defs);
		self.binding.typ = self.binding.typ.infer_to(&self.body.typ);
	}
}

impl<'src> ExprMeta<'src> {
	fn set_type(&mut self, set: Type<'src>) {
		self.typ = set;
	}

	fn infer_types(&mut self,
		parent_expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		let found_type = {
			let expected_type = self.typ.add_constraint(parent_expected_type);

			// TODO: Move this step to Expr::infer_types
			match *self.val {
				Expr::Nil(_) => Type::new_nil(),
				// TODO: Add inference for these
				Expr::VarDef(_) | Expr::Assign(_) => Type::new_nil(),
				// TODO: This should be an internal, more general integer type
				Expr::NumLit(_, _) => Type::new_basic("i64"),
				// TODO: This should be a construct somehow
				Expr::StrLit(_, _) => Type::new_basic("&str"),
				Expr::Bool(_, _) => Type::new_basic("bool"),
				Expr::Binding(ref path) => {
					path.infer_types(&expected_type, var_types, const_defs);
					path.get_type(&expected_type, var_types, const_defs)
				},
				Expr::SExpr(ref mut sexpr) => {
					sexpr.infer_types(&expected_type, var_types, const_defs);
					sexpr.body_type().clone()
				},
				Expr::Block(ref mut block) => {
					block.infer_types(&expected_type, var_types, const_defs);
					block.get_type().clone()
				},
				Expr::Cond(ref mut cond) => {
					cond.infer_types(&expected_type, var_types, const_defs);
					cond.get_type().clone()
				},
				Expr::Lambda(ref mut lambda) => {
					lambda.infer_types(&expected_type, var_types, const_defs);
					lambda.get_type()
				},
				Expr::Symbol(_, _) => Type::Symbol,
			}
		};

		self.set_type(found_type);
	}
}

impl<'src> AST<'src> {
	pub fn infer_types(&mut self) {
		let mut const_defs = ConstDefs::new();

		// Push the module scope on top of the stack
		let mut const_defs = const_defs.map_push_local(
			&mut self.const_defs,
			|it| it.map(|(k, v)| (k, Some(v))),
			|it| it.map(|(k, v)| (k, v.unwrap())));

		const_defs.do_for_item_at_height("main", 0, |const_defs, main|
			main.infer_types(&Type::new_nil(), &mut Vec::new(), const_defs));
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_Type_infer_to() {
	}

	#[test]
	fn test_Type_infer_by() {
	}

	#[test]
	fn test_Type_add_constraint() {
	}

	#[test]
	fn test_constrain_related_types() {
	}

	#[test]
	fn test_Path_get_type() {
	}

	#[test]
	fn test_Path_infer_types() {
	}

	#[test]
	fn test_ConstDef_infer_types() {
	}

	#[test]
	fn test_SExpr_body_type() {
	}

	#[test]
	fn test_SExpr_infer_arg_types() {
	}

	#[test]
	fn test_SExpr_infer_types() {
	}

	#[test]
	fn test_Block_get_type() {
	}

	#[test]
	fn test_Block_infer_types() {
	}

	#[test]
	fn test_Cond_infer_types() {
	}

	#[test]
	fn test_inferred_to_polymorphic() {
	}

	#[test]
	fn test_Lambda_infer_arg_types() {
	}

	#[test]
	fn test_Lambda_get_type() {
	}

	#[test]
	fn test_Lambda_infer_types() {
	}

	#[test]
	fn test_VarDef_infer_types() {
	}

	#[test]
	fn test_ExprMeta_set_type() {
	}

	#[test]
	fn test_ExprMeta_infer_types() {
	}

	#[test]
	fn test_AST_infer_types() {
	}
}
