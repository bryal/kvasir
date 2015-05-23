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

use std::mem::replace;
use super::{ ConstDef, ConstDefOrType, ConstDefScope, ConstDefScopeStack,
	Type, TypedBinding, Expr, ExprMeta, Path, Env };
use super::core_lib::core_consts;

impl Path {
	fn get_type<'a>(&self, env: &'a Env) -> Option<&'a Type> {
		if let Some(ident) = self.ident() {
			if let Some(ty) = env.core_consts.get(ident) {
				Some(ty)
			} else if let Some((def, _)) = env.const_defs.get(ident) {
				def.get_type()
			} else if let Some(var_stack_ty) = env.get_var_type(ident) {
				var_stack_ty
			} else {
				panic!("Path::get_type: Unresolved path `{}`", ident)
			}
		} else {
			panic!("Path::get_type: Not implemented for anything but simple idents")
		}
	}

	fn infer_types(&self, expected_type: Option<&Type>, env: &mut Env) {
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
			} else if expected_type.is_some() {
				if let Some(stack_bnd_ty) = env.get_var_type_mut(ident) {
					// Path is a var
					if stack_bnd_ty.is_none() {
						*stack_bnd_ty = expected_type.cloned()
					} else if stack_bnd_ty.as_ref() != expected_type {
						// TODO: Shouldn't necessarily panic if types differ.
						//       Add some kind of coercion and polymorphism.
						panic!(
							"Path::infer_types: Tried to set type of binding on stack to `{:?}` \
								when it already had type `{:?}`",
								expected_type.unwrap(),
							stack_bnd_ty.as_ref().unwrap())
					}
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
	fn infer_types(&mut self, env: &mut Env) {
		let prev_var_types = replace(&mut env.var_types, Vec::new());

		self.body.infer_types(self.binding.type_sig.as_ref(), env);

		env.var_types = prev_var_types;

		match (&mut self.binding.type_sig, self.body.type_.as_ref()) {
			(&mut Some(ref expected), Some(found)) if expected != found => panic!(
				"ConstDef::infer_types: Type mismatch. Expected `{:?}`, found `{:?}`",
				expected,
				found),
			(b @ &mut None, Some(found)) => *b = Some(found.clone()),
			(&mut None, None) => panic!("ConstDef::infer_types: No type could be infered"),
			_ => ()
		}
	}
}

/// Extract a function type signature in the form of <→ arg1 arg2 body> to (&[arg1, arg2], body)
fn extract_fn_sig(sig: &Type) -> (&[Type], &Type) {
	match sig {
		&Type::Construct(ref c, ref ts) if c == "fn" || c == "→" => (ts.init(), ts.last().unwrap()),
		t => panic!("extract_fn_sig: `{:?}` is not a function type", t),
	}
}

impl super::SExpr {
	fn body_type(&self) -> Option<&Type> {
		self.func.type_.as_ref().map(extract_fn_sig).map(|(_, body_t)| body_t)
	}

	fn infer_arg_types(&mut self, expected_types: Option<&[Type]>, env: &mut Env) {
		if let Some(expected_types) = expected_types {
			if self.args.len() != expected_types.len() {
				panic!("SExpr::infer_arg_types: Arity mismatch. Expected {}, found {}",
					expected_types.len(),
					self.args.len())
			}

			for (arg, expect_ty) in self.args.iter_mut().zip(expected_types) {
				arg.infer_types(Some(expect_ty), env);
			}
		} else {
			for arg in self.args.iter_mut() {
				arg.infer_types(None, env);
			}
		}
	}

	fn infer_types(&mut self, parent_expected_type: Option<&Type>, env: &mut Env) {
		self.infer_arg_types(None, env);

		// TODO: Partial inference when not all bindings have type signatures
		let expected_fn_type = if self.args.iter().all(|arg| arg.type_.is_some())
			&& parent_expected_type.is_some()
		{
			Some(Type::fn_sig(self.args.iter()
				.map(|tb| tb.type_.clone().unwrap())
				.collect(),
				parent_expected_type.unwrap().clone()))
		} else {
			None
		};

		println!("Inferring {:?}, expects {:?}", self.func, expected_fn_type);

		self.func.infer_types(expected_fn_type.as_ref(), env);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce
		match (self.func.type_.clone(), expected_fn_type) {
			(Some(Type::Construct(_, fn_arg_types)), None) =>
				// `init` because last arg in fn sig is return type
				self.infer_arg_types(Some(fn_arg_types.init()), env),
			(Some(ty), None) => panic!("SExpr::infer_types: `{:?}` is not a function type", ty),
			(Some(ref found_ty), Some(ref expected_ty)) if found_ty != expected_ty => panic!(
				"SExpr::infer_types: Function type mismatch. Expected `{:?}`, found `{:?}`",
				expected_ty,
				found_ty),
			(None, None) => panic!("SExpr::infer_types: Could not infer type for function"),
			_ => ()
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
	fn get_type(&self) -> Option<&Type> {
		self.exprs.last().expect("Block::get_type: No expressions in block").type_.as_ref()
	}

	fn infer_types(&mut self, parent_expected_type: Option<&Type>, env: &mut Env) {
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
				_ => expr.infer_types(None, env)
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
				expr.infer_types(None, env);
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
	fn infer_types(&mut self, parent_expected_type: Option<&Type>, env: &mut Env) {
		// TODO: Use predicates to infer var types

		if parent_expected_type.is_none() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(Some(&Type::bool()), env);
			}
			for consequence in self.iter_consequences_mut() {
				if consequence.type_.is_some() || {
					consequence.infer_types(None, env);
					consequence.type_.is_some()
				} {
					found_type = Some(consequence.type_.clone());
				}
			}

			match found_type {
				Some(expected_type) =>
					self.infer_types(expected_type.as_ref(), env),
				// TODO: Shouldn't panic here. Even if type can't be infered now,
				//       parent might return later with an expected type.
				None => panic!("Cond::infer_types: Could not infer type for any clause"),
			}
		} else {
			let t_bool = &Type::bool();

			for &mut (ref mut predicate, ref mut consequence) in self.clauses.iter_mut() {
				predicate.infer_types(Some(t_bool), env);
				consequence.infer_types(parent_expected_type, env);
			}
			if let Some(ref mut else_clause) = self.else_clause {
				else_clause.infer_types(parent_expected_type, env);
			}
		}
	}
}

impl super::Lambda {
	fn set_arg_types(&mut self, arg_types: &[Type]) {
		for ((arg_name, arg_type_sig), set_type) in self.arg_bindings.iter_mut()
			.map(|tb| (&tb.ident, &mut tb.type_sig))
			.zip(arg_types)
		{
			match *arg_type_sig {
				None => *arg_type_sig = Some(set_type.clone()),
				Some(ref ty) if ty != set_type => panic!(
					"ConstDef::set_arg_types: Tried to assign type `{:?}` to arg `{}`, \
						but it was already of type `{:?}`",
					set_type,
					arg_name,
					ty),
				_ => ()
			}
		}
	}

	fn get_type(&self) -> Option<Type> {
		if self.arg_bindings.iter().all(|tb| tb.type_sig.is_some()) {
			self.body.type_.as_ref().map(|body_ty| Type::fn_sig(
				self.arg_bindings.iter()
					.cloned()
					.map(|tb| tb.type_sig.unwrap())
					.collect(),
				body_ty.clone()))
		} else {
			None
		}
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self, expected_type: Option<&Type>, env: &mut Env) {
		let expected_body_type = expected_type.map(extract_fn_sig)
			.map(|(fn_arg_types, fn_body_type)| {
				self.set_arg_types(fn_arg_types);
				fn_body_type
			});

		let (vars_len, args_len) = (env.var_types.len(), self.arg_bindings.len());

		env.var_types.extend(self.arg_bindings.drain(..));

		self.body.infer_types(expected_body_type, env);

		assert_eq!(env.var_types.len(), vars_len + args_len);

		self.arg_bindings.extend(env.var_types.drain(vars_len..));
	}
}

impl super::VarDef {
	// NOTE: This is very similar to ConstDef::infer_types, DRY?
	fn infer_types(&mut self, env: &mut Env) {
		self.body.infer_types(self.binding.type_sig.as_ref(), env);

		match (&mut self.binding.type_sig, self.body.type_.as_ref()) {
			(&mut Some(ref expected), Some(found)) if expected != found => panic!(
				"VarDef::infer_types: Type mismatch. Expected `{:?}`, found `{:?}`",
				expected,
				found),
			(b @ &mut None, Some(found)) => *b = Some(found.clone()),
			(&mut None, None) => panic!("VarDef::infer_types: No type could be infered"),
			_ => ()
		}
	}
}

impl ExprMeta {
	fn infer_types(&mut self, parent_expected_type: Option<&Type>, env: &mut Env) {
		let found_type = {
			let expected_type = self.type_.as_ref().or(parent_expected_type);

			match *self.value {
				// Doesn't have children to infer types for
				Expr::Nil => Some(Type::nil()),
				// TODO: This should be an internal, more general integer type
				Expr::NumLit(_) => Some(Type::basic("u64")),
				// TODO: This should be a construct somehow
				Expr::StrLit(_) => Some(Type::basic("&str")),
				Expr::Bool(_) => Some(Type::bool()),
				Expr::Binding(ref path) => {
					path.infer_types(expected_type, env);
					path.get_type(env).cloned()
				},
				Expr::SExpr(ref mut sexpr) => {
					sexpr.infer_types(expected_type, env);
					sexpr.body_type().cloned()
				},
				Expr::Block(ref mut block) => {
					block.infer_types(expected_type, env);
					block.get_type().cloned()
				},
				Expr::Cond(ref mut cond) => {
					cond.infer_types(expected_type, env);
					cond.get_type().cloned()
				},
				Expr::Lambda(ref mut lambda) => {
					lambda.infer_types(expected_type, env);
					lambda.get_type()
				},
				Expr::VarDef(_) | Expr::Assign(_) => Some(Type::nil()),
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
