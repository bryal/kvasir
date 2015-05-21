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

use std::iter::{ repeat, FromIterator };
use super::{ ConstDef, ConstDefMap, Type, TypedBinding, Item, Expr, ExprMeta, Path };

impl super::ConstDef {
	fn infer_types(&mut self, const_defs: &mut ConstDefMap, caller_stack: &mut Vec<&str>) {
		self.body.infer_types(
			self.binding.type_sig.as_ref(),
			const_defs,
			&mut Vec::new(),
			caller_stack);

		match (self.binding.type_sig, self.body.type_) {
			(Some(expected), Some(found)) if expected != found => panic!(
				"ConstDef::infer_types: Type mismatch. Expected `{:?}`, found `{:?}`",
				expected,
				found),
			(None, Some(found)) => self.binding.type_sig = Some(found),
			(None, None) => panic!("ConstDef::infer_types: No type could be infered"),
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

	fn infer_arg_types(&mut self,
		expected_types: Option<&[Type]>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		if let Some(expected_types) = expected_types {
			for (arg, expect_ty) in self.args.iter_mut().zip(expected_types) {
				arg.infer_types(Some(expect_ty), const_defs, var_stack, caller_stack);
			}
		} else {
			for arg in self.args.iter_mut() {
				arg.infer_types(None, const_defs, var_stack, caller_stack);
			}
		}
	}

	fn infer_types(&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		self.infer_arg_types(None, const_defs, var_stack, caller_stack);

		// TODO: Partial inference when not all bindings have type signatures
		let expected_fn_type = if self.args.iter().all(|arg| arg.type_.is_some())
			&& parent_expected_type.is_some()
		{
			Some(Type::construct(
				"→",
				self.args.iter().map(|tb| tb.type_.clone().unwrap()).collect()))
		} else {
			None
		};

		self.func.infer_types(expected_fn_type.as_ref(), const_defs, var_stack, caller_stack);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce
		match (self.func.type_, expected_fn_type) {
			(Some(Type::Construct(_, ref fn_arg_types)), None) =>
				self.infer_arg_types(Some(fn_arg_types), const_defs, var_stack, caller_stack),
			(Some(found_ty), None) =>
				panic!("SExpr::infer_types: `{:?}` is not a function type", found_ty),
			(Some(found_ty), Some(expected_ty)) if found_ty != expected_ty => panic!(
				"SExpr::infer_types: Function type mismatch. Expected `{:?}`, found `{:?}`",
				expected_ty,
				found_ty),
			(None, None) => panic!("SExpr::infer_types: Could not infer type for function"),
		}
	}
}

impl super::Block {
	fn get_type(&self) -> Option<&Type> {
		self.exprs.last().expect("Block::get_type: No expressions in block").type_.as_ref()
	}

	fn infer_types(&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		/// Moves all values in `to_add` to `map`, creating a union of the two maps.
		/// Return the paths of `to_add`. If a key from `to_add` already exists in `map`, panic.
		fn add_defs<'a>(map: &mut ConstDefMap<'a>, (paths, to_add): (&'a [Path], &mut Vec<ConstDef>)) {
			if paths.iter().all(|path| map.contains_key(path)) {
				for (key, val) in paths.iter().zip(to_add.drain(..)) {
					map.insert(key, val);
				}
			} else {
				panic!(
					"Block::infer_types::add_defs: Key already exists in map, `{}`",
					paths.iter().find(|path| map.contains_key(path)).unwrap())
			}
		}

		/// Subtract all entries in `map` of keys in `keys` and return the difference.
		fn subtract_keys_to<'a>(map: &mut ConstDefMap, keys: &[Path], to: &mut Vec<ConstDef>) {
			if let Some(not_found) = keys.iter().find(|key| map.contains_key(key)) {
				panic!(
					"Block::infer_types::subtract_keys_to: Key doesn't exist in map, `{}`",
					not_found);
			} else {
				to.extend(keys.iter().map(|key| map.remove(key).unwrap()))
			}
		}

		if self.exprs.len() == 0 {
			return;
		}

		let const_paths: Vec<_> = self.const_defs.iter()
			.map(|def| Path::new(vec![def.binding.ident.into()], false))
			.collect();
		add_defs(const_defs, (&const_paths, &mut self.const_defs));

		let old_vars_len = var_stack.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in self.exprs.init_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr.expr() {
				var_def.infer_types(const_defs, var_stack, caller_stack);

				var_stack.push(var_def.binding);
			} else {
				expr.infer_types(None, const_defs, var_stack, caller_stack);
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().unwrap()
				.infer_types(parent_expected_type, const_defs, var_stack, caller_stack);
		}

		let block_defined_vars = var_stack.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in self.exprs.init_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr.expr() {
				var_def.infer_types(const_defs, var_stack, caller_stack);

				var_stack.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(None, const_defs, var_stack, caller_stack);
			}
		}

		if self.exprs.last_mut().unwrap().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().unwrap()
				.infer_types(parent_expected_type, const_defs, var_stack, caller_stack);
		}

		subtract_keys_to(const_defs, &const_paths, &mut self.const_defs);
	}
}

impl super::Cond {
	fn infer_types(&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		for (predicate, consequence) in self.clauses.iter_mut()
			.map(|&mut (ref mut p, ref mut c)| (p, c))
			.chain(self.else_clause.iter_mut().map(|c| (&mut ExprMeta::new_true(), c)))
		{
			predicate.infer_types(Some(&Type::bool()), const_defs, var_stack, caller_stack);
			consequence.infer_types(parent_expected_type, const_defs, var_stack, caller_stack);
		}

		if parent_expected_type.is_none() {
			match self.clauses.iter()
				.map(|&(_, ref c)| c)
				.chain(self.else_clause.iter())
				.find(|clause| clause.type_sig.is_some())
				.map(|t| t.cloned())
			{
				Some(expected_type) => if !self.clauses.iter().map(|&(_, ref c)| c)
					.chain(self.else_clause.iter())
					.all(|clause| clause.type_sig.is_some())
				{
					self.infer_types(expected_type.as_ref(), const_defs, var_stack, caller_stack)
				},
				None => panic!("Cond::infer_types: Could not infer type for any clause"),
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
					ty)
			}
		}
	}

	fn get_type(&self) -> Option<&Type> {
		Some(Type::fn_sig(
			self.arg_bindings.iter()
				.cloned()
				.map(|tb| tb.type_sig.expect("Lambda::get_type: Arg lacks type"))
				.collect(),
			self.body.type_.clone().expect("Lambda::get_type: Body has no type")))
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self,
		expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		caller_stack: &mut Vec<&str>)
	{
		if let Some((fn_arg_types, fn_body_type)) = expected_type.map(extract_fn_sig) {
			// Type signature already exists. Just infer types for body and make sure
			// there are no collisions

			self.set_arg_types(fn_arg_types);

			self.body.infer_types(Some(fn_body_type), const_defs, &mut self.arg_bindings);
		} else {
			// No type signature for function binding. Pass arg bindings to body and infer types
			// for body, then get function signature from updated arg types and body type

			let arg_bindings_old_len = self.arg_bindings.len();

			// args: type_to_infer_to, const_defs, var_stack
			self.body.infer_types(None, const_defs, &mut self.arg_bindings);

			assert_eq!(self.arg_bindings.len(), arg_bindings_old_len);
		}
	}
}

impl super::VarDef {
	fn infer_types(
		&mut self,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		self.body.infer_types(self.binding.type_sig.as_ref(), const_defs, &mut Vec::new());

		match (self.binding.type_sig, self.body.type_) {
			(Some(expected), Some(found)) if expected != found => panic!(
				"ConstDef::infer_types: Type mismatch. Expected `{:?}`, found `{:?}`",
				expected,
				found),
			(None, Some(found)) => self.binding.type_sig = Some(found),
			(None, None) => panic!("ConstDef::infer_types: No type could be infered"),
		}
	}
}

/// Checks binding stack for the type of binding `bnd` and resolves conflicts.
/// If expected type is None, return stack type. If stack type is None, update stack type
/// with to expected type. If both are Some but differ in value, panic.
fn resolve_var_type<'a>(var_stack: &'a mut [TypedBinding], bnd: &str, expected_ty: Option<&'a Type>)
	-> Option<&'a Type>
{
	fn get_stack_binding_type<'a>(var_stack: &'a mut [TypedBinding], bnd: &str)
		-> &'a mut Option<Type>
	{
		&mut var_stack.iter_mut()
			.rev()
			.find(|stack_bnd| stack_bnd.ident == bnd)
			.expect(format!("get_stack_binding_type: Binding not in stack, `{}`", bnd))
			.type_sig
	}

	fn update_binding_stack(var_stack: &mut [TypedBinding], bnd: &str, expected_ty: &Type) {
		let stack_bnd_ty = get_stack_binding_type(var_stack, bnd);

		if stack_bnd_ty.is_none() {
			*stack_bnd_ty = Some(expected_ty.clone())
		} else if stack_bnd_ty.as_ref() != Some(expected_ty) {
			// TODO: Shouldn't necessarily panic if types differ. Add some sort of coercion and polymorphism.
			panic!(
				"update_binding_stack: Tried to set type of binding on stack to `{:?}` \
					when it already had type `{:?}`",
				expected_ty,
				stack_bnd_ty.as_ref().unwrap())
		}
	}

	match expected_ty {
		Some(ty) => {
			update_binding_stack(var_stack, bnd, ty);
			expected_ty
		},
		None => get_stack_binding_type(var_stack, bnd).as_ref(),
	}
}

fn resolve_const_type<'a>(
	const_defs: &'a mut ConstDefMap,
	path: &Path,
	expected_type: Option<&'a Type>) -> Option<&'a Type>
{
	fn get_const_def<'a>(const_defs: &'a mut ConstDefMap, path: &Path) -> &'a mut ConstDef {
		const_defs.get_mut(path).expect(format!("get_const_def: No entry exists for `{}`", path))
	}

	match expected_type {
		Some(ty) => {
			get_const_def(const_defs, path).set_type(ty);
			expected_type
		},
		None => get_const_def(const_defs, path).get_type(),
	}
}

impl ExprMeta {
	fn infer_types(&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>,
		caller_stack: &mut Vec<&str>)
	{
		let expected_type = self.coerce_type.as_ref().or(parent_expected_type);

		let found_type = match *self.value {
			// Doesn't have children to infer types for
			Expr::Nil => Some(&Type::nil()),
			// TODO: This should be an internal, more general integer type
			Expr::NumLit(_) => Some(&Type::basic("u64")),
			// TODO: This should be a construct somehow
			Expr::StrLit(_) => Some(&Type::basic("&str")),
			Expr::Binding(ref path) => resolve_var_type(var_stack, path, expected_type)
				.or_else(resolve_const_type(const_defs, path, expected_type)),
			Expr::SExpr(ref mut sexpr) => {
				sexpr.infer_types(expected_type, var_stack);
				sexpr.body_type()
			},
			Expr::Block(ref mut block) => {
				block.infer_types(expected_type, var_stack);
				block.type_sig.as_ref()
			},
			Expr::Cond(ref mut cond) => {
				cond.infer_types(expected_type, var_stack);
				cond.type_sig.as_ref()
			},
			Expr::Lambda(ref mut lambda) => {
				lambda.infer_types(expected_type, var_stack);
				lambda.type_sig.as_ref()
			},
		};

		self.set_type(found_type);
	}
}

impl super::AST {
	pub fn infer_types(&mut self) {
		if let Some(main_def) = self.items.iter_mut()
			.find(|meta| if let Item::ConstDef(ref def) = *meta.item {
				def.binding.ident == "main"
			} else {
				false
			})
		{
			main_def.infer_types(&mut self.items).unwrap()
		} else {
			panic!("AST::infer_types: No main function found")
		}
	}
}
