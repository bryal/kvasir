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
use std::iter::repeat;
use std::borrow::Cow;
use super::{ ConstDef, ConstDefOrType, ConstDefScope, ConstDefScopeStack,
	Type, TypedBinding, Expr, ExprMeta, Path, Env, assign_type };
use super::core_lib::core_consts;

impl Path {
	fn get_type<'a>(&self, specialize_to: &'a Type, env: &'a Env) -> Cow<'a, Type> {
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

		general.specialize_by(specialize_to)
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
					assign_type(stack_bnd_ty, Cow::Borrowed(expected_type))
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

		self.body.infer_types(&self.binding.type_sig, env);

		env.var_types = prev_var_types;

		assign_type(&mut self.binding.type_sig, Cow::Borrowed(&self.body.type_))
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
	fn body_type(&self) -> &Type {
		extract_fn_sig(&self.func.type_).1
	}

	fn infer_arg_types(&mut self, env: &mut Env) {
		let inferreds = if self.func.type_.is_inferred() {
			vec![Type::Inferred; self.args.len()]
		} else {
			vec![]
		};
		let expected_types = if self.func.type_.is_specified() {
			extract_fn_sig(&self.func.type_).0
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

		let expected_fn_type = Type::fn_sig(
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
	fn infer_types(&mut self, expected_type: &Type, env: &mut Env) {
		if expected_type.is_inferred() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::bool(), env);
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
				predicate.infer_types(&Type::bool(), env);
				consequence.infer_types(expected_type, env);
			}
			if let Some(ref mut else_clause) = self.else_clause {
				else_clause.infer_types(expected_type, env);
			}
		}
	}
}

impl super::Lambda {
	fn set_arg_types(&mut self, set_arg_types: &[Type]) {
		for (arg, set_type) in self.arg_bindings.iter_mut().zip(set_arg_types) {
			if set_type.is_inferred() {
				assign_type(
					&mut arg.type_sig,
					Cow::Owned(Type::Poly(format!("__Poly{}", arg.ident))))
			}
		}
	}

	fn get_type(&self) -> Type {
		Type::fn_sig(
			self.arg_bindings.iter().map(|tb| tb.type_sig.clone()).collect(),
			self.body.type_.clone())
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self, mut expected_type: Cow<Type>, env: &mut Env) {
		if expected_type.is_inferred() {
			expected_type = Cow::Owned(Type::fn_sig(
				self.arg_bindings.iter().map(|tb| tb.type_sig.clone()).collect(),
				self.body.type_.clone()));
		}

		let (fn_arg_types, fn_body_type) = extract_fn_sig(&expected_type);

		self.set_arg_types(fn_arg_types);

		let (vars_len, args_len) = (env.var_types.len(), self.arg_bindings.len());

		env.var_types.extend(self.arg_bindings.drain(..));

		self.body.infer_types(fn_body_type, env);

		assert_eq!(env.var_types.len(), vars_len + args_len);

		self.arg_bindings.extend(env.var_types.drain(vars_len..));
	}
}

impl super::VarDef {
	fn infer_types(&mut self, env: &mut Env) {
		self.body.infer_types(&self.binding.type_sig, env);

		assign_type(&mut self.binding.type_sig, Cow::Borrowed(&self.body.type_))
	}
}

impl ExprMeta {
	fn infer_types(&mut self, parent_expected_type: &Type, env: &mut Env) {
		let found_type = {
			let expected_type = self.type_.or(parent_expected_type);

			match *self.value {
				// Doesn't have children to infer types for
				Expr::Nil => Type::nil(),
				// TODO: This should be an internal, more general integer type
				Expr::NumLit(_) | Expr::VarDef(_) | Expr::Assign(_) => Type::basic("u64"),
				// TODO: This should be a construct somehow
				Expr::StrLit(_) => Type::basic("&str"),
				Expr::Bool(_) => Type::bool(),
				Expr::Binding(ref path) => {
					path.infer_types(expected_type, env);
					path.get_type(expected_type, env).into_owned()
				},
				Expr::SExpr(ref mut sexpr) => {
					sexpr.infer_types(expected_type, env);
					sexpr.body_type().clone()
				},
				Expr::Block(ref mut block) => {
					block.infer_types(expected_type, env);
					block.get_type().clone()
				},
				Expr::Cond(ref mut cond) => {
					cond.infer_types(expected_type, env);
					cond.get_type().clone()
				},
				Expr::Lambda(ref mut lambda) => {
					lambda.infer_types(Cow::Borrowed(expected_type), env);
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
