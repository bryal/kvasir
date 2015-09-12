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

use lib::compiler_messages::*;
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
	pub fn is_unknown(&self) -> bool {
		match *self {
			Type::Unknown => true,
			_ => false
		}
	}
	pub fn is_partially_known(&self) -> bool {
		! self.is_unknown()
	}
	pub fn is_fully_known(&self) -> bool {
		match *self {
			Type::Unknown => false,
			Type::Basic(_) => true,
			Type::Construct(_, ref args) => args.iter().all(Type::is_fully_known),
		}
	}

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

	/// Recursively infer all `Unknown` by the `by` type.
	/// If types are incompatible, e.g. `(Vec Inferred)` v. `(Option Int32)`, return `None`
	fn infer_by(&self, by: &Self) -> Option<Self> {
		match (self, by) {
			(_, _) if self == by => Some(self.clone()),
			(_, &Type::Unknown) => Some(self.clone()),
			(&Type::Unknown, _) => Some(by.clone()),
			(&Type::Construct(ref s1, ref as1), &Type::Construct(ref s2, ref as2)) if s1 == s2 =>
				as1.iter()
					.zip(as2.iter())
					.map(|(a1, a2)| a1.infer_by(a2))
					.collect::<Option<_>>()
					.map(|args| Type::Construct(s1.clone(), args)),
			(_, _) => None,
		}
	}
}

impl<'src> ConstDef<'src> {
	fn get_type(&self) -> &Type<'src> {
		&self.body.typ
	}

	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Type<'src> {
		match self.body.infer_types(expected_ty, var_types, const_defs) {
			Ok(ty) => ty,
			Err(found_ty) => src_error_panic!(&self.pos,
				format!("Type mismatch. Expected `{}`, found `{}`", expected_ty, found_ty))
		}
	}
}

impl<'src> Path<'src> {
	/// Get the type of the item bound to by `self`. If
	fn get_type(&self, var_types: &[TypedBinding<'src>], const_defs: &ConstDefs<'src>)
		-> Type<'src>
	{
		if let Some(ident) = self.ident() {
			if let Some(ty) = CORE_CONSTS_TYPES.get(ident) {
				ty.clone()
			} else if let Some((def, _)) = const_defs.get(ident) {
				def.as_ref().map_or(Type::Unknown, |e| e.get_type().clone())
			} else if let Some(var_stack_ty) = get_var_type(var_types, ident) {
				var_stack_ty.clone()
			} else {
				src_error_panic!(&self.pos, format!("Unresolved path `{}`", ident))
			}
		} else {
			panic!("Path::get_type: Not implemented for anything but simple idents")
		}
	}

	fn infer_types(&self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		if let Some(ident) = self.ident() {
			if let Some(core_ty) = CORE_CONSTS_TYPES.get(ident) {
				// Don't infer types for core items. Just check compatibility with expected_ty

				core_ty.infer_by(expected_ty).ok_or(core_ty.clone())
			} else if let Some(height) = const_defs.get_height(ident) {
				// Path is a constant

				if const_defs.get_at_height(ident, height).unwrap().is_some() {
					const_defs.do_for_item_at_height(ident, height, |const_defs, def|
						Ok(def.infer_types(expected_ty, &mut Vec::new(), const_defs).clone()))
				} else {
					// We are currently doing inference inside this definition

					Ok(Type::Unknown)
				}
			} else {
				if let Some(stack_bnd_ty) = get_var_type_mut(var_types, ident) {
					// Path is a var

					stack_bnd_ty.infer_by(expected_ty)
						.map(|infered_ty| {
							*stack_bnd_ty = infered_ty.clone();
							infered_ty
						})
						.ok_or(stack_bnd_ty.clone())
				} else {
					src_error_panic!(&self.pos, format!("Unresolved path `{}`", ident))
				}
			}
		} else {
			panic!("Path::infer_types: Not implemented for anything but simple idents")
		}
	}
}

/// Extract a function type signature in the form of (prod param1  ... paramn body)
/// to (&[param1, ..., paramn], body)
fn unpack_proc_typ<'src, 't>(sig: &'t Type<'src>) -> Option<(&'t [Type<'src>], &'t Type<'src>)> {
	match sig {
		&Type::Construct("proc", ref ts) => ts.split_last().map(|(b, ps)| (ps, b)),
		_ => None,
	}
}

impl<'src> SExpr<'src> {
	fn body_type(&self) -> &Type<'src> {
		unpack_proc_typ(&self.proced.typ).expect("SExpr::body_type: Could not extract fn sig").1
	}

	fn infer_arg_types(&mut self,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		let expected_types = if self.proced.typ.is_partially_known() {
			// The type of the procedure is not unknown.
			// If it's a valid procedure type, use it for inference

			match unpack_proc_typ(&self.proced.typ) {
				Some((param_tys, _)) if param_tys.len() == self.args.len() =>
					param_tys.iter().collect(),
				Some((param_tys, _)) => src_error_panic!(&self.pos,
					format!("Arity mismatch. Expected {}, found {}",
						param_tys.len(),
						self.args.len())),
				None => src_error_panic!(&self.proced.pos(),
					format!("Type mismatch. Expected procedure, found `{}`", self.proced.typ)),
			}
		} else {
			vec![&self.proced.typ; self.args.len()]
		};

		for (arg, expect_ty) in self.args.iter_mut().zip(expected_types) {
			if let Err(err_ty) = arg.infer_types(expect_ty, var_types, const_defs) {
				src_error_panic!(arg.pos(),
					format!("Type mismatch. Expected `{}`, found `{}`", expect_ty, err_ty));
			}
		}
	}

	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> &Type<'src> {
		self.infer_arg_types(var_types, const_defs);

		let expected_proc_type = Type::new_proc(
			self.args.iter().map(|tb| tb.typ.clone()).collect(),
			expected_ty.clone());

		self.proced.infer_types(&expected_proc_type, var_types, const_defs);

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if self.proced.typ.is_partially_known() {
			// If type of `self.proced` hasn't been infered,
			// there's no new data to help with infence
			self.infer_arg_types(var_types, const_defs);
		}
		
		unpack_proc_typ(&self.proced.typ).unwrap().1
	}
}

impl<'src> Block<'src> {
	fn get_type(&self) -> &Type<'src> {
		&self.exprs.last().expect("Block::get_type: No expressions in block").typ
	}

	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Type<'src> {
		let (init, last) = if let Some((last, init)) = self.exprs.split_last_mut() {
			if last.val.is_var_def() {
				src_error_panic!(
					last.pos(),
					"Block ended with variable definition");
			}
			(init, last)
		} else {
			return Type::nil()
		};

		let mut const_defs = const_defs.map_push_local(
			&mut self.const_defs,
			|it| it.map(|(k, v)| (k, Some(v))),
			|it| it.map(|(k, v)| (k, v.unwrap())));

		let old_vars_len = var_types.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in init.iter_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr.val {
				var_def.infer_types(var_types, &mut const_defs);
				var_types.push(var_def.binding.clone());
			} else {
				expr.infer_types(&Type::Unknown, var_types, &mut const_defs).unwrap();
			}
		}
		last.infer_types(expected_ty, var_types, &mut const_defs);

		let mut block_defined_vars = var_types.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in init {
			if let Expr::VarDef(ref mut var_def) = *expr.val {
				var_def.infer_types(var_types, &mut const_defs);
				var_types.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(&Type::Unknown, var_types, &mut const_defs);
			}
		}
		last.infer_types(expected_ty, var_types, &mut const_defs);

		last.typ.clone()
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
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		// TODO: Verify everything is still correct
		if expected_type.is_unknown() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::Basic("bool"), var_types, const_defs);
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

			match found_type {
				Some(ref expected_type) => self.infer_types(expected_type, var_types, const_defs),
				None => Ok(Type::Unknown)
			}
		} else {
			for &mut (ref mut predicate, ref mut consequence) in self.clauses.iter_mut() {
				predicate.infer_types(&Type::Basic("bool"), var_types, const_defs);
				consequence.infer_types(expected_type, var_types, const_defs);
			}
			match self.else_clause {
				Some(ref mut else_clause) =>
					else_clause.infer_types(expected_type, var_types, const_defs),
				None => Ok(Type::Unknown)
			}
		}
	}
}

impl<'src> Lambda<'src> {
	fn infer_arg_types<'a, It: IntoIterator<Item=&'a Type<'src>>>(&mut self, expected_params: It)
		where 'src: 'a
	{
		for (param, expected_param) in self.params.iter_mut().zip(expected_params) {
			match param.typ.infer_by(&expected_param) {
				Some(infered) => param.typ = infered,
				None => src_error_panic!(&param.pos,
					format!("Type mismatch. Expected `{}`, found `{}`", expected_param, param.typ))
			}
		}
	}

	fn get_type(&self) -> Type<'src> {
		Type::new_proc(
			self.params.iter().map(|tb| tb.typ.clone()).collect(),
			self.body.typ.clone())
	}

	// TODO: Add support for enviroment capturing closures
	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		let (expected_params, expected_body) = match unpack_proc_typ(expected_ty) {
			Some((params, _)) if params.len() != self.params.len() => return Err(self.get_type()),
			Some((params, body)) => (params.iter().collect(), body),
			None if *expected_ty == Type::Unknown => (
				vec![expected_ty; self.params.len()],
				expected_ty,
			),
			None => return Err(self.get_type()),
		};

		// Own type is `Unknown` if no type has been infered yet, or none was inferable

		if self.body.typ.is_partially_known()
			|| self.params.iter().all(|tb| tb.typ.is_partially_known())
		{
			// Not unknown. Only infer further if expected_ty provides something new

			if let Some((infered_params, infered_body)) = self.params.iter()
				.zip(expected_params.iter())
				.map(|(param_tb, expected)| param_tb.typ.infer_by(expected))
				.collect::<Option<Vec<_>>>()
				.and_then(|infered_params| self.body.typ.infer_by(expected_body)
					.map(|infered_body| (infered_params, infered_body)))
			{
				if self.body.typ == infered_body
					&& self.params.iter()
						.zip(infered_params)
						.all(|(param, infered_param)| param.typ == infered_param)
				{
					// Own type can't be infered further by `expected_ty`
					return Ok(self.get_type());
				}
			} else {
				// Own type and expected type are not compatible. Type mismatch
				return Err(self.get_type());
			}
		}

		self.infer_arg_types(expected_params);

		let (vars_len, n_params) = (var_types.len(), self.params.len());

		var_types.extend(self.params.clone());

		self.body.infer_types(&expected_body, var_types, const_defs);

		assert_eq!(var_types.len(), vars_len + n_params);

		for (param, found) in self.params.iter_mut()
			.zip(var_types.drain(vars_len..))
			.map(|(param, found)| (&mut param.typ, found.typ))
		{
			*param = found;
		}
		Ok(self.get_type())
	}
}

impl<'src> VarDef<'src> {
	fn infer_types(&mut self,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>)
	{
		match self.body.infer_types(&self.binding.typ, var_types, const_defs) {
			Ok(body_ty) =>  self.binding.typ = body_ty.clone(),
			Err(found) => src_error_panic!(&self.pos,
				format!("Type mismatch. Expected `{}`, found `{}`", self.binding.typ, found))
		}
	}
}

impl<'src> Expr<'src> {
	/// On success, return expected, infered type. On failure, return unexpected, found type
	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		match *self {
			Expr::Nil(_) => expected_ty.infer_by(&Type::nil()).ok_or(Type::nil()),
			Expr::VarDef(ref mut def) => if expected_ty.infer_by(&Type::nil()).is_some() {
				def.infer_types(var_types, const_defs);
				Ok(Type::nil())
			} else {
				Err(Type::nil())
			},
			Expr::Assign(_) => expected_ty.infer_by(&Type::nil()).ok_or(Type::nil()),
			Expr::NumLit(_, ref pos) => match *expected_ty {
				Type::Unknown
					| Type::Basic("Int8") | Type::Basic("UInt8")
					| Type::Basic("Int16") | Type::Basic("UInt16")
					| Type::Basic("Int32") | Type::Basic("UInt32") | Type::Basic("Float32")
					| Type::Basic("Int64") | Type::Basic("UInt64") | Type::Basic("Float64")
					=> Ok(expected_ty.clone()),
				_ => Err(Type::Basic("numeric literal"))
			},
			Expr::StrLit(_, _) => {
				let u8_slice = Type::Construct("Slice", vec![Type::Basic("UInt8")]);
				expected_ty.infer_by(&u8_slice).ok_or(u8_slice)
			},
			Expr::Bool(_, _) => expected_ty.infer_by(&Type::Basic("Bool"))
				.ok_or(Type::Basic("Bool")),
			Expr::Binding(ref path) => path.infer_types(&expected_ty, var_types, const_defs),
			Expr::SExpr(ref mut sexpr) =>
				Ok(sexpr.infer_types(&expected_ty, var_types, const_defs).clone()),
			Expr::Block(ref mut block) =>
				Ok(block.infer_types(&expected_ty, var_types, const_defs)),
			Expr::Cond(ref mut cond) => cond.infer_types(&expected_ty, var_types, const_defs),
			Expr::Lambda(ref mut lambda) => lambda.infer_types(&expected_ty, var_types, const_defs),
			Expr::Symbol(_, _) => expected_ty.infer_by(&Type::Basic("Symbol"))
				.ok_or(Type::Basic("Symbol")),
		}
	}
}

/// On type mismatch, return mismatched, found type as `Err`.
/// Otherwise, return type of `self` as `Ok`
impl<'src> ExprMeta<'src> {
	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		// Own type is `Unknown` if no type has been infered yet, or none was inferable

		if self.typ.is_partially_known() {
			if let Some(infered) = expected_ty.infer_by(&self.typ) {
				if self.typ == infered {
					// Own type can't be infered further by `expected_ty`
					return Ok(self.typ.clone());
				}
			} else {
				// Own type and expected type are not compatible. Type mismatch
				return Err(self.typ.clone());
			}
		}
		// Own type is unknown, or `expected_ty` is more known than own type

		// Fill in the gaps of `expect_ty` using own type ascription, if any
		let expected_ty = if let Some(ref ty_ascription) = self.ty_ascription {
			match expected_ty.infer_by(&ty_ascription.0) {
				Some(infered) => infered,
				None => return Err(ty_ascription.0.clone()),
			}
		} else {
			expected_ty.clone()
		};

		let found_type = try!(self.val.infer_types(&expected_ty, var_types, const_defs));

		self.typ = found_type.clone();

		Ok(found_type)
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
			main.infer_types(&Type::nil(), &mut Vec::new(), const_defs));
	}
}
