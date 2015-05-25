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

use std::collections::HashMap;
use std::mem::replace;
use std::borrow::Cow;
use super::*;
use super::core_lib::core_consts;

type ConstDefScope = HashMap<String, ConstDefOrType>;

type ConstDefScopeStack = ScopeStack<String, ConstDefOrType>;

struct Env {
	core_consts: HashMap<&'static str, Type>,
	const_defs: ConstDefScopeStack,
	var_types: Vec<TypedBinding>
}
impl Env {
	fn get_var_type(&self, ident: &str) -> Option<&Type> {
		self.var_types.iter()
			.rev()
			.find(|stack_tb| stack_tb.ident == ident)
			.map(|stack_tb| &stack_tb.type_sig)
	}
	fn get_var_type_mut(&mut self, bnd: &str) -> Option<&mut Type> {
		self.var_types.iter_mut()
			.rev()
			.find(|stack_tb| stack_tb.ident == bnd)
			.map(|stack_tb| &mut stack_tb.type_sig)
	}
}

enum ConstDefOrType {
	Def(ConstDef),
	Type(Type),
}
impl ConstDefOrType {
	fn get_type(&self) -> &Type {
		match self {
			&ConstDefOrType::Def(ref def) => &def.binding.type_sig,
			&ConstDefOrType::Type(ref ty) => &ty
		}
	}

	/// Extracts a mutable ConstDef reference from self if self is of variant Def. Else, panic.
	fn as_def(&mut self) -> Option<&mut ConstDef> {
		match self {
			&mut ConstDefOrType::Def(ref mut def) => Some(def),
			_ => None
		}
	}

	/// If variant is Def, return contained ConstDef. Panic otherwise
	fn unwrap_def(self) -> ConstDef {
		match self {
			ConstDefOrType::Def(def) => def,
			_ => panic!("ConstDefOrType::into_def: Variant wasn't `Def`")
		}
	}

	/// If variant is `Def`, replace def with `Type` and return def
	fn replace_into_def(&mut self) -> Option<ConstDef> {
		let ty = match self.as_def() {
			Some(def) => def.binding.type_sig.clone(),
			None => return None
		};

		Some(replace(self, ConstDefOrType::Type(ty)).unwrap_def())
	}

	/// If variant is `Type`, replace self with `Def` variant containing passed def. Panic otherwise
	fn insert_def(&mut self, def: ConstDef) {
		match self {
			&mut ConstDefOrType::Type(_) => *self = ConstDefOrType::Def(def),
			_ => panic!("ConstDefOrType::insert_def: `self` is already `Type`")
		}
	}
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
				if s1 == s2
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
				if s1 == s2
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
	fn get_type(&self, constraint: &Type, env: &Env) -> Type {
		let general = if let Some(ident) = self.ident() {
			if let Some(ty) = env.core_consts.get(ident) {
				ty
			} else if let Some((def, _)) = env.const_defs.get(ident) {
				def.get_type()
			} else if let Some(var_stack_ty) = env.get_var_type(ident) {
				var_stack_ty
			} else {
				panic!("Path::get_type: Unresolved path `{}`", ident)
			}
		} else {
			panic!("Path::get_type: Not implemented for anything but simple idents")
		};
		// Fill in the blanks. A known type can't be inferred to be an unknown type
		general.add_constraint(&constraint.infer_by(general)).into_owned()
	}

	fn infer_types(&self, expected_type: &Type, env: &mut Env) {
		if let Some(ident) = self.ident() {
			if env.core_consts.get(ident).is_some() {
				// Don't try to infer types for internal functions
				()
			} else if let Some(height) = env.const_defs.get_height(ident) {
				// Path is a constant
				let above = env.const_defs.split_from(height + 1);

				if let Some(mut def) = env.const_defs.get_at_height_mut(ident, height)
					.unwrap()
					.replace_into_def()
				{
					def.infer_types(env);

					env.const_defs.get_at_height_mut(ident, height).unwrap().insert_def(def);
				}

				env.const_defs.extend(above);
			} else if expected_type.is_specified() {
				if let Some(stack_bnd_ty) = env.get_var_type_mut(ident) {
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

impl super::ConstDef {
	fn get_type(&self) -> &Type {
		&self.binding.type_sig
	}

	fn set_type(&mut self, ty: Type) {
		self.binding.type_sig = ty
	}

	fn infer_types(&mut self, env: &mut Env) {
		let prev_var_types = replace(&mut env.var_types, Vec::new());

		self.body.infer_types(&self.binding.type_sig, env);

		env.var_types = prev_var_types;

		self.binding.type_sig = self.body.type_
			.add_constraint(&self.binding.type_sig.infer_by(&self.body.type_))
			.into_owned();
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

impl super::SExpr {
	fn body_type(&self) -> &Type {
		extract_fn_sig(&self.func.type_).expect("SExpr::body_type: Could not extract fn sig").1
	}

	fn infer_arg_types(&mut self, env: &mut Env) {
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
			arg.infer_types(expect_ty, env);
		}
	}

	fn infer_types(&mut self, parent_expected_type: &Type, env: &mut Env) {
		self.infer_arg_types(env);

		let expected_fn_type = Type::new_fn(
			self.args.iter().map(|tb| tb.type_.clone()).collect(),
			parent_expected_type.clone());

		self.func.infer_types(&expected_fn_type, env);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if self.func.type_.is_specified() {
			self.infer_arg_types(env);
		}
	}
}

/// Maps a Vec<ConstDef> to a ConstDefScope
fn vec_to_def_scope(defs_vec: Vec<ConstDef>) -> ConstDefScope {
	let mut scope = ConstDefScope::new();
	for def in defs_vec.into_iter() {
		let key = def.binding.ident.clone();
		scope.insert(key, ConstDefOrType::Def(def));
	}

	scope
}

/// Maps a ConstDefScope to a Vec<ConstDef>
fn def_scope_to_vec(scope: ConstDefScope) -> Vec<ConstDef> {
	scope.into_iter().map(|(_, def)| def.unwrap_def()).collect()
}

impl super::Block {
	fn get_type(&self) -> &Type {
		&self.exprs.last().expect("Block::get_type: No expressions in block").type_
	}

	fn infer_types(&mut self, parent_expected_type: &Type, env: &mut Env) {
		if self.exprs.len() == 0 {
			return;
		}

		env.const_defs.push(vec_to_def_scope(replace(&mut self.const_defs, Vec::new())));

		let old_vars_len = env.var_types.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in self.exprs.init_mut() {
			match expr {
				&mut ExprMeta{ value: box Expr::VarDef(ref mut var_def), .. } => {
					var_def.infer_types(env);
					env.var_types.push(var_def.binding.clone());
				},
				_ => expr.infer_types(&Type::Inferred, env)
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().unwrap()
				.infer_types(parent_expected_type, env);
		}

		let mut block_defined_vars = env.var_types.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in self.exprs.init_mut() {
			if let &mut ExprMeta{ value: box Expr::VarDef(ref mut var_def), .. } = expr {
				var_def.infer_types(env);

				env.var_types.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(&Type::Inferred, env);
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().unwrap()
				.infer_types(parent_expected_type, env);
		}

		self.const_defs = def_scope_to_vec(env.const_defs.pop()
			.expect("Block::infer_types: Could not pop const def scope stack"));
	}
}

impl super::Cond {
	fn get_type(&self) -> &Type {
		match self.iter_consequences().map(|c| &c.type_).find(|ty| ty.is_specified()) {
			Some(found) => found,
			None => &self.iter_consequences().next().unwrap().type_
		}
	}

	fn infer_types(&mut self, expected_type: &Type, env: &mut Env) {
		if expected_type.is_inferred() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::new_bool(), env);
			}
			for consequence in self.iter_consequences_mut() {
				if consequence.type_.is_specified() || {
					consequence.infer_types(&Type::Inferred, env);
					consequence.type_.is_specified()
				} {
					found_type = Some(consequence.type_.clone());
					break;
				}
			}

			if let Some(ref expected_type) = found_type {
				self.infer_types(expected_type, env)
			}
		} else {
			for &mut (ref mut predicate, ref mut consequence) in self.clauses.iter_mut() {
				predicate.infer_types(&Type::new_bool(), env);
				consequence.infer_types(expected_type, env);
			}
			if let Some(ref mut else_clause) = self.else_clause {
				else_clause.infer_types(expected_type, env);
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

impl super::Lambda {
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
	fn infer_types(&mut self, constraint: &Type, env: &mut Env) {
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

		let (vars_len, args_len) = (env.var_types.len(), self.arg_bindings.len());

		env.var_types.extend(inferred_to_polymorphic(self.arg_bindings.clone()));

		self.body.infer_types(&body_constraint, env);

		assert_eq!(env.var_types.len(), vars_len + args_len);

		for (arg, found) in self.arg_bindings.iter_mut()
			.zip(env.var_types.drain(vars_len..))
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

impl super::VarDef {
	fn infer_types(&mut self, env: &mut Env) {
		self.body.infer_types(&self.binding.type_sig, env);
		self.binding.type_sig = self.binding.type_sig.infer_to(&self.body.type_).into_owned();
	}
}

impl ExprMeta {
	fn set_type(&mut self, set: Type) {
		self.type_ = set;
	}

	fn infer_types(&mut self, parent_expected_type: &Type, env: &mut Env) {
		let found_type = {
			let expected_type = self.type_.add_constraint(parent_expected_type);

			match *self.value {
				// Doesn't have children to infer types for
				Expr::Nil => Type::new_nil(),
				// TODO: This should be an internal, more general integer type
				Expr::NumLit(_) | Expr::VarDef(_) | Expr::Assign(_) => Type::new_basic("i64"),
				// TODO: This should be a construct somehow
				Expr::StrLit(_) => Type::new_basic("&str"),
				Expr::Bool(_) => Type::new_bool(),
				Expr::Binding(ref path) => {
					path.infer_types(&expected_type, env);
					path.get_type(&expected_type, env)
				},
				Expr::SExpr(ref mut sexpr) => {
					sexpr.infer_types(&expected_type, env);
					sexpr.body_type().clone()
				},
				Expr::Block(ref mut block) => {
					block.infer_types(&expected_type, env);
					block.get_type().clone()
				},
				Expr::Cond(ref mut cond) => {
					cond.infer_types(&expected_type, env);
					cond.get_type().clone()
				},
				Expr::Lambda(ref mut lambda) => {
					lambda.infer_types(&expected_type, env);
					lambda.get_type()
				},
			}
		};

		self.set_type(found_type);
	}
}

impl super::AST {
	pub fn infer_types(&mut self) {
		let mut const_defs = ConstDefScopeStack::new();

		// Push the module scope on top of the stack
		const_defs.push(vec_to_def_scope(replace(&mut self.const_defs, Vec::new())));

		let mut main = match const_defs.get_at_height_mut("main", 0) {
			Some(main) => main.replace_into_def().unwrap(),
			None => panic!("AST::infer_types: No main function found")
		};

		let mut env = Env{
			core_consts: core_consts(),
			const_defs: const_defs,
			var_types: Vec::new()
		};

		main.infer_types(&mut env);

		env.const_defs.get_at_height_mut("main", 0).unwrap().insert_def(main);

		if env.const_defs.height() != 1 {
			panic!("AST::infer_types: Stack is not single scope");
		}

		self.const_defs = def_scope_to_vec(env.const_defs.pop().unwrap())
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
