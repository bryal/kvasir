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
use lib::*;
use super::*;
use super::core_lib::CORE_CONSTS_TYPES;

type ConstDefs = ScopeStack<String, Option<ExprMeta>>;

fn get_var_type<'a>(var_types: &'a [TypedBinding], ident: &str) -> Option<&'a Type> {
	var_types.iter().rev().find(|tb| tb.ident == ident).map(|tb| &tb.type_sig)
}
fn get_var_type_mut<'a>(var_types: &'a mut Vec<TypedBinding>, bnd: &str) -> Option<&'a mut Type> {
	var_types.iter_mut().rev().find(|tb| tb.ident == bnd).map(|tb| &mut tb.type_sig)
}

impl Type {
	/// Recursively infer all Inferred to the `to` type.
	/// If types are different and not inferrable, panic.
	fn infer_to<'a>(&'a self, to: &'a Type) -> Cow<Type> {
		match (self, to) {
			(_, _) if self == to => Cow::Borrowed(self),
			(&Type::Inferred, _) => Cow::Borrowed(to),
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				Cow::Owned(Type::Construct(
					s1.clone(),
					as1.iter()
						.zip(as2.iter())
						.map(|(a1, a2)| a1.infer_to(a2).into_owned()).collect())),
			(&Type::Tuple(ref as1), &Type::Tuple(ref as2)) =>
				Cow::Owned(Type::Tuple(as1.iter()
					.zip(as2.iter())
					.map(|(a1, a2)| a1.infer_to(a2).into_owned()).collect())),
			_ => panic!("Type::infer_to: Can't infer {:?} to {:?}", self, to),
		}
	}

	/// Recursively infer all Inferred by the `by` type. If types are different and not inferrable,
	/// just ignore and return self
	fn infer_by<'a>(&'a self, by: &'a Type) -> Cow<'a, Type> {
		match (self, by) {
			(_, _) if self == by => Cow::Borrowed(self),
			(&Type::Inferred, _) => Cow::Borrowed(by),
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				Cow::Owned(Type::Construct(
					s1.clone(),
					as1.iter()
						.zip(as2.iter())
						.map(|(a1, a2)| a1.infer_by(a2).into_owned()).collect())),
			(&Type::Tuple(ref as1), &Type::Tuple(ref as2)) =>
				Cow::Owned(Type::Tuple(as1.iter()
					.zip(as2.iter())
					.map(|(a1, a2)| a1.infer_by(a2).into_owned()).collect())),
			(_, _) => Cow::Borrowed(self),
		}
	}

	fn specialize_to<'a>(&'a self, constraint: &'a Type) -> Cow<Type> {
		match (self, constraint) {
			(_, _) if self == constraint => Cow::Borrowed(self),
			(&Type::Inferred, _) => panic!("Type::specialize_to: Can't specialize unknown type"),
			(_, &Type::Inferred) => panic!("Type::specialize_to: Constraint is unknown"),
			(&Type::Basic(_), &Type::Basic(_)) if self == constraint => Cow::Borrowed(self),
			(&Type::Construct(ref s1, ref gens), &Type::Construct(ref s2, ref specs)) =>
				if Type::constructor_eq(s1, s2)
			{
				Cow::Owned(Type::Construct(s1.clone(), constrain_related_types(gens, specs)))
			} else {
				panic!("Type::specialize_to: Type constructors differ. {:?} != {:?}", s1, s2)
			},
			(&Type::Tuple(ref gens), &Type::Tuple(ref specs)) =>
				Cow::Owned(Type::Tuple(constrain_related_types(gens, specs))),
			(&Type::Poly(_), _) => Cow::Borrowed(constraint),
			(_, &Type::Poly(_)) => Cow::Borrowed(self),
			_ => panic!("Type::specialize_to: Can't specialize {:?} into {:?}", self, constraint),
		}
	}

	fn add_constraint<'a>(&'a self, constraint: &'a Type) -> Cow<Type> {
		match (self, constraint) {
			(_, _) if self == constraint => Cow::Borrowed(self),
			(&Type::Inferred, _) => Cow::Borrowed(constraint),
			(_, &Type::Inferred) => Cow::Borrowed(self),
			(&Type::Basic(_), &Type::Basic(_)) if self == constraint => Cow::Borrowed(self),
			(&Type::Construct(ref s1, ref gens), &Type::Construct(ref s2, ref specs)) =>
				if Type::constructor_eq(s1, s2)
			{
				Cow::Owned(Type::Construct(s1.clone(), constrain_related_types(gens, specs)))
			} else {
				panic!("Type::add_constraint: Type constructors differ. {:?} != {:?}", s1, s2)
			},
			(&Type::Tuple(ref gens), &Type::Tuple(ref specs)) =>
				Cow::Owned(Type::Tuple(constrain_related_types(gens, specs))),
			(&Type::Poly(_), _) => Cow::Borrowed(constraint),
			(_, &Type::Poly(_)) => Cow::Borrowed(self),
			_ => panic!("Type::add_constraint: Can't specialize {:?} into {:?}", self, constraint),
		}
	}
}

fn constrain_related_types(generals: &[Type], criteria: &[Type]) -> Vec<Type> {
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
				*same = (&*constrained).clone();
			}
		} else {
			constraining[i] = constraining[i].add_constraint(criterium).into_owned();
		}
	}

	constraining
}

impl Path {
	fn get_type(&self, constraint: &Type, var_types: &[TypedBinding], const_defs: &ConstDefs)
		-> Type
	{
		let general = if let Some(ident) = self.ident() {
			if let Some(ty) = CORE_CONSTS_TYPES.get(ident) {
				Cow::Borrowed(ty)
			} else if let Some((def, _)) = const_defs.get(ident) {
				def.as_ref().map_or(Cow::Owned(Type::Inferred), |e| Cow::Borrowed(e.get_type()))
			} else if let Some(var_stack_ty) = get_var_type(var_types, ident) {
				Cow::Borrowed(var_stack_ty)
			} else {
				panic!("Path::get_type: Unresolved path `{}`", ident)
			}
		} else {
			panic!("Path::get_type: Not implemented for anything but simple idents")
		};
		// Fill in the blanks. A known type can't be inferred to be an unknown type
		general.add_constraint(&constraint.infer_by(&general)).into_owned()
	}

	fn infer_types(&self, expected_type: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
	{
		if let Some(ident) = self.ident() {
			if CORE_CONSTS_TYPES.get(ident).is_some() {
				// Don't try to infer types for internal functions
				()
			} else if let Some(height) = const_defs.get_height(ident) {
				// Path is a constant
				if const_defs.get_at_height(ident, height).unwrap().is_some() {
					const_defs.do_for_item_at_height(ident, height, |const_defs, def|
						def.infer_types(&Type::Inferred, &mut Vec::new(), const_defs))
				}
			} else if expected_type.is_specified() {
				if let Some(stack_bnd_ty) = get_var_type_mut(var_types, ident) {
					// Path is a var
					*stack_bnd_ty = stack_bnd_ty.infer_by(expected_type)
						.add_constraint(expected_type)
						.into_owned();
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
fn extract_fn_sig(sig: &Type) -> Option<(&[Type], &Type)> {
	match sig {
		&Type::Construct(ref c, ref ts) if c == "fn" || c == "→" =>
			Some((ts.init(), ts.last().unwrap())),
		_ => None,
	}
}

impl SExpr {
	fn body_type(&self) -> &Type {
		extract_fn_sig(&self.func.type_).expect("SExpr::body_type: Could not extract fn sig").1
	}

	fn infer_arg_types(&mut self, var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs) {
		let inferreds = if self.func.type_.is_inferred() {
			vec![Type::Inferred; self.args.len()]
		} else {
			vec![]
		};

		let expected_types = if self.func.type_.is_specified() {
			extract_fn_sig(&self.func.type_)
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

	fn infer_types(&mut self, parent_expected_type: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
	{
		self.infer_arg_types(var_types, const_defs);

		let expected_fn_type = Type::new_fn(
			self.args.iter().map(|tb| tb.type_.clone()).collect(),
			parent_expected_type.clone());

		self.func.infer_types(&expected_fn_type, var_types, const_defs);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if self.func.type_.is_specified() {
			self.infer_arg_types(var_types, const_defs);
		}
	}
}

impl Block {
	fn get_type(&self) -> &Type {
		&self.exprs.last().expect("Block::get_type: No expressions in block").type_
	}

	fn infer_types(&mut self, parent_expected_type: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
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
				&mut ExprMeta{ value: box Expr::VarDef(ref mut var_def), .. } => {
					var_def.infer_types(var_types, &mut const_defs);
					var_types.push(var_def.binding.clone());
				},
				_ => expr.infer_types(&Type::Inferred, var_types, &mut const_defs)
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
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
			if let &mut ExprMeta{ value: box Expr::VarDef(ref mut var_def), .. } = expr {
				var_def.infer_types(var_types, &mut const_defs);

				var_types.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(&Type::Inferred, var_types, &mut const_defs);
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut()
				.unwrap()
				.infer_types(parent_expected_type, var_types, &mut const_defs);
		}
	}
}

impl Cond {
	fn get_type(&self) -> &Type {
		match self.iter_consequences().map(|c| &c.type_).find(|ty| ty.is_specified()) {
			Some(found) => found,
			None => &self.iter_consequences().next().unwrap().type_
		}
	}

	fn infer_types(&mut self, expected_type: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
	{
		if expected_type.is_inferred() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::new_basic("bool"), var_types, const_defs);
			}
			for consequence in self.iter_consequences_mut() {
				if consequence.type_.is_specified() || {
					consequence.infer_types(&Type::Inferred, var_types, const_defs);
					consequence.type_.is_specified()
				} {
					found_type = Some(consequence.type_.clone());
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
		if bind.type_sig.is_inferred() {
			bind.type_sig = Type::Poly(format!("__Poly{}", bind.ident));
		}
	}

	binds
}

impl Lambda {
	fn infer_arg_types(&mut self, constraints: &[Type]) {
		for (arg, constraint) in self.arg_bindings.iter_mut().zip(constraints) {
			arg.type_sig = arg.type_sig.infer_to(constraint).into_owned();
		}
	}

	fn get_type(&self) -> Type {
		Type::new_fn(
			self.arg_bindings.iter().map(|tb| tb.type_sig.clone()).collect(),
			self.body.type_.clone())
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self, constraint: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
	{
		let body_constraint =
			if let Some((args_constraints, body_constraint)) = extract_fn_sig(constraint)
		{
			self.infer_arg_types(args_constraints);

			self.body.type_.infer_by(body_constraint)
				.add_constraint(body_constraint)
				.into_owned()
		} else {
			self.body.type_.clone()
		};

		let (vars_len, args_len) = (var_types.len(), self.arg_bindings.len());

		var_types.extend(inferred_to_polymorphic(self.arg_bindings.clone()));

		self.body.infer_types(&body_constraint, var_types, const_defs);

		assert_eq!(var_types.len(), vars_len + args_len);

		for (arg, found) in self.arg_bindings.iter_mut()
			.zip(var_types.drain(vars_len..))
			.map(|(arg, found)| (&mut arg.type_sig, found.type_sig))
		{
			let inferred = arg.infer_by(&found).into_owned();
			if inferred == found {
				*arg = inferred;
			} else {
				panic!("Lambda::infer_types: Function signature doesn't match actual type");
			}
		}
	}
}

impl VarDef {
	fn infer_types(&mut self, var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs) {
		self.body.infer_types(&self.binding.type_sig, var_types, const_defs);
		self.binding.type_sig = self.binding.type_sig.infer_to(&self.body.type_).into_owned();
	}
}

impl ExprMeta {
	fn set_type(&mut self, set: Type) {
		self.type_ = set;
	}

	fn infer_types(&mut self, parent_expected_type: &Type,
		var_types: &mut Vec<TypedBinding>, const_defs: &mut ConstDefs)
	{
		let found_type = {
			let expected_type = self.type_.add_constraint(parent_expected_type);

			// TODO: Move this step to Expr::infer_types
			match *self.value {
				Expr::Nil => Type::new_nil(),
				// TODO: Add inference for these
				Expr::VarDef(_) | Expr::Assign(_) => Type::new_nil(),
				// TODO: This should be an internal, more general integer type
				Expr::NumLit(_) => Type::new_basic("i64"),
				// TODO: This should be a construct somehow
				Expr::StrLit(_) => Type::new_basic("&str"),
				Expr::Bool(_) => Type::new_basic("bool"),
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
			}
		};

		self.set_type(found_type);
	}
}

impl AST {
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
