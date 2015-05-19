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
// Like: foo calling bar calling baz calling foo => ERROR

// TODO: Consider redisigning this module. Maybe have an Inferer that takes expressions instead
// of implementing inference for each expression type.

use std::collections::{ HashMap, HashSet };
use std::hash::Hash;
use super::{ FnDef, Item, Type, TypedBinding, Expr, ExprMeta, Path };

/// A map of constant definitions
type ConstDefMap = HashMap<&Path, FnDef>;

impl super::FnDef {
	// TODO: Infer types for incomplete function sig. E.g. inc: <→ u32 _> => inc: <→ u32 u32>
	fn infer_types(&mut self, const_defs: ConstDefMap) {
		let mut arg_bindings = self.arg_bindings.clone();

		if let Some((fn_arg_types, fn_body_type)) = self.extract_type_sig() {
			// Type signature already exists. Just infer types for body and make sure
			// there are no collisions

			self.set_arg_types(fn_arg_types);

			self.body.infer_types(Some(fn_body_type), const_defs, &mut arg_bindings);
		} else {
			// No type signature for function binding. Pass arg bindings to body and infer types
			// for body, then get function signature from updated arg types and body type

			let arg_bindings_old_len = arg_bindings.len();

			// args: type_to_infer_to, const_defs, var_stack
			self.body.infer_types(None, const_defs, &mut arg_bindings);

			if arg_bindings.len() != arg_bindings_old_len {
				panic!("FnDef::infer_types: arg_bindings.len() != arg_bindings_old_len");
			}

			let arg_types = arg_bindings.into_iter()
				.map(|b| b.type_sig.expect("FnDef::infer_types: Arg has no type"))
				.collect();

			self.set_arg_types(&mut arg_types);

			self.construct_fn_sig(
				arg_types,
				self.body.type_sig.expect("FnDef::infer_types: Body has no type"));
		}
	}
}

/// Extract a function type signature in the form of <→ arg1 arg2 body> to (&[arg1, arg2], body)
fn extract_fn_sig(sig: &Type) -> (&[Type], &Type) {
	match sig {
		&Type::Construct(ref c, ref ts) if c == "fn" || c == "→" => (ts.init(), ts.last()),
		t => panic!("extract_fn_sig: `{:?}` is not a function type", t),
	}
}

impl super::SExpr {
	fn body_type(&self) -> Option<&Type> {
		self.func.type_sig.as_ref().map(extract_fn_sig).map(|(_, body_t)| body_t)
	}

	fn infer_types(
		&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>)
	{
		self.infer_arg_types(None, const_defs, var_stack);

		// TODO: Partial inference when not all bindings have type signatures
		let expected_fn_type = if self.args.iter().all(TypedBinding::has_type)
			&& parent_expected_type.is_some()
		{
			Some(Type::construct("→", self.args.iter().map(|tb| tb.type_sig).collect()))
		} else {
			None
		};

		self.func.infer_types(expected_fn_type, const_defs, var_stack);

		let found_fn_type = self.func.type_sig;

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce
		if found_fn_type.is_some() && expected_fn_type.is_none() {
			if let Type::Construct(_, ref fn_arg_types) = found_fn_type {
				self.infer_arg_types(Some(fn_arg_types), const_defs, var_stack);
			} else {
				panic!("SExpr::infer_types: `{:?}` is not a function type", found_fn_type);
			}
		} else if found_fn_type.is_none() {
			panic!("SExpr::infer_types: Could not infer type for function");
		} else if found_fn_type != expected_fn_type {
			panic!(
				"SExpr::infer_types: Function type mismatch. Expected `{:?}`, found `{:?}`",
				expected_fn_type,
				found_fn_type);
		}
	}
}

/// Moves all values in `rhs` to `main`, creating a union of the two maps.
/// If a key from `rhs` already exists in `main`, return `rhs` as an error.
/// On success, return the HashSet of the keys of `rhs`
fn join_map<K: Hash+Eq, V, S>(main: &mut HashMap<K, V, S>, rhs: HashMap<K, V, S>)
	-> Result(HashSet<K>, HashMap<K, V, S>)
{
	if rhs.keys().all(|key| main.contains_key(key)) {
		let mut set = HashSet::with_capacity(rhs.len());

		for (key, val) in rhs {
			main.insert(key, val);
			set.insert(key);
		}

		Ok(set)
	} else {
		Err(rhs)
	}
}

/// Subtract all entries in `map` of keys in `keys` and return the difference.
fn subtract_map<K: Hash+Eq, V, S>(map: &mut HashMap<K, V, S>, keys: &HashSet<K>)
	-> Option<HashMap<K, V>>
{
	if keys.iter().all(|key| map.contains_key(key)) {
		Some(HashMap::from_iter(keys.iter().map(|key| (key, map.remove(key).unwrap()))))
	} else {
		None
	}
}

impl super::Block {
	fn get_type(&self) -> Option<&Type> {
		self.exprs.last().type_sig.as_ref()
	}
	fn infer_types(
		&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>)
	{
		let constant_keys = join_map(const_defs, self.constant_defs.drain());

		let old_vars_len = var_stack.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in self.exprs.init_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr {
				var_def.infer_types(const_defs, var_stack);

				var_stack.push(var_def.binding);
			} else {
				expr.infer_types(None, const_defs, var_stack);
			}
		}

		if self.exprs.last_mut().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().infer_types(parent_expected_type, const_defs, var_stack);
		}

		let block_defined_vars = var_stack.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in self.exprs.init_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr {
				var_def.infer_types(const_defs, var_stack);

				var_stack.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(None, const_defs, var_stack);
			}
		}

		if self.exprs.last_mut().expr().is_var_def() {
			panic!("Block::infer_types: Last expression in block is var definition")
		} else {
			self.exprs.last_mut().infer_types(parent_expected_type, const_defs, var_stack);
		}

		self.constant_defs = subtract_map(const_defs, constant_keys);
	}
}

impl super::Cond {
	fn infer_types(
		&mut self,
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

/// Checks binding stack for the type of binding `bnd` and resolves conflicts.
/// If expected type is None, return stack type. If stack type is None, update stack type
/// with to expected type. If both are Some but differ in value, panic.
fn resolve_var_type(var_stack: &mut [TypedBinding], bnd: &str, expected_ty: Option<&Type>)
	-> Option<&Type>
{
	fn get_stack_binding_type<'a>(var_stack: &mut [TypedBinding], bnd: &str) -> &mut Option<Type> {
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

fn resolve_const_type(const_defs: &mut ConstDefMap, path: &Path, expected_type: Option<&Type>)
	-> Option<&Type>
{
	fn get_const_def(const_defs: &mut ConstDefMap, path: &Path) -> &mut FnDef {
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
	fn infer_types(
		&mut self,
		parent_expected_type: Option<&Type>,
		const_defs: &mut ConstDefMap,
		var_stack: &mut Vec<TypedBinding>)
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
				.or(resolve_const_type(const_defs, path, expected_type)),
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
			.find(|meta| if let Item::FnDef(ref def) = *meta.item {
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
