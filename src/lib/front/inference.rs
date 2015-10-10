
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

//! Type inference

// TODO: Almost all `infer_types` takes const map + var stack + caller stack.
//       Maybe encapsulate this using some kind of state
// TODO: Replace verbose type error checks with:
//       `foo.infer_types(...)
//           .unwrap_or_else(foo.pos().type_mismatcher(expected_ty))`

use std::fmt::{ self, Display };
use lib::front::parse::*;
use lib::collections::ScopeStack;
use super::core_lib::CORE_CONSTS_TYPES;
use super::SrcPos;
use self::InferenceErr::*;

enum InferenceErr<'p, 'src: 'p> {
	/// Type mismatch. (expected, found)
	TypeMis(&'p Type<'src>, &'p Type<'src>),
}
impl<'src, 'p> Display for InferenceErr<'src, 'p> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			TypeMis(expected, found) =>
				write!(f, "Type mismatch. Expected `{}`, found `{}`", expected, found)
		}
	}
}

type ConstDefs<'src> = ScopeStack<&'src str, Option<ConstDef<'src>>>;

fn get_var_type<'src, 't>(var_types: &'t [TypedBinding<'src>], ident: &str)
	-> Option<&'t Type<'src>>
{
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
	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Type<'src> {
		self.body.infer_types(expected_ty, var_types, const_defs)
			.unwrap_or_else(|found_ty| self.body.pos().error(TypeMis(expected_ty, &found_ty)))
	}
}

impl<'src> Path<'src> {
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
					self.pos.error(format!("Unresolved path `{}`", ident))
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
				Some((param_tys, _)) => self.pos.error(
					format!("Arity mismatch. Expected {}, found {}",
						param_tys.len(),
						self.args.len())),
				None => self.proced.pos().error(
					TypeMis(
						&Type::new_proc(vec![Type::Unknown], Type::Unknown),
						&self.proced.typ)),
			}
		} else {
			vec![&self.proced.typ; self.args.len()]
		};

		for (arg, expect_ty) in self.args.iter_mut().zip(expected_types) {
			if let Err(ref err_ty) = arg.infer_types(expect_ty, var_types, const_defs) {
				arg.pos().error(TypeMis(expect_ty, err_ty));
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

		if let Err(err_ty) = self.proced.infer_types(&expected_proc_type, var_types, const_defs) {
			self.proced.pos().error(TypeMis(&expected_proc_type, &err_ty));
		}
		

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if self.proced.typ.is_partially_known() {
			// If type of `self.proced` hasn't been infered,
			// there's no new data to help with infence
			self.infer_arg_types(var_types, const_defs);
		}

		self.body_type()
	}
}

impl<'src> Block<'src> {
	fn infer_types(&mut self,
		expected_ty: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Type<'src> {
		let (init, last) = if let Some((last, init)) = self.exprs.split_last_mut() {
			if last.val.is_var_def() {
				last.pos().error("Block ended with variable definition");
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

		last.infer_types(expected_ty, var_types, &mut const_defs)
			.unwrap_or_else(|err_ty| last.pos().error(TypeMis(expected_ty, &err_ty)));

		let mut block_defined_vars = var_types.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in init {
			if let Expr::VarDef(ref mut var_def) = *expr.val {
				var_def.infer_types(var_types, &mut const_defs);
				var_types.push(block_defined_vars.next().unwrap());
			} else {
				expr.infer_types(&Type::Unknown, var_types, &mut const_defs)
					.unwrap_or_else(|err_ty| expr.pos().error(TypeMis(&Type::Unknown, &err_ty)));
			}
		}
		last.infer_types(expected_ty, var_types, &mut const_defs)
			.unwrap_or_else(|err_ty| last.pos().error(TypeMis(expected_ty, &err_ty)));

		last.typ.clone()
	}
}

impl<'src> Cond<'src> {
	fn infer_types(&mut self,
		expected_type: &Type<'src>,
		var_types: &mut Vec<TypedBinding<'src>>,
		const_defs: &mut ConstDefs<'src>
	) -> Result<Type<'src>, Type<'src>> {
		// TODO: Verify everything is still correct
		if expected_type.is_unknown() {
			let mut found_type = None;

			for predicate in self.iter_predicates_mut() {
				predicate.infer_types(&Type::Basic("bool"), var_types, const_defs)
					.unwrap_or_else(|err_ty|
						predicate.pos().error(TypeMis(&Type::Basic("Bool"), &err_ty)));
			}
			for consequence in self.iter_consequences_mut() {
				if consequence.typ.is_partially_known() || {
					consequence.infer_types(&Type::Unknown, var_types, const_defs)
						.unwrap_or_else(|err_ty|
							consequence.pos().error(TypeMis(&Type::Unknown, &err_ty)));
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
				predicate.infer_types(&Type::Basic("bool"), var_types, const_defs)
					.unwrap_or_else(|err_ty|
						predicate.pos().error(TypeMis(&Type::Basic("bool"), &err_ty)));
				consequence.infer_types(expected_type, var_types, const_defs)
					.unwrap_or_else(|err_ty|
						consequence.pos().error(TypeMis(expected_type, &err_ty)));
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
				None => param.pos.error(TypeMis(expected_param, &param.typ))
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

		if self.get_type().is_partially_known() {
			if let Some(infered) = expected_ty.infer_by(&self.get_type()) {
				if self.get_type() == infered {
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

		self.body.infer_types(&expected_body, var_types, const_defs)
			.unwrap_or_else(|err_ty| self.body.pos().error(TypeMis(expected_body, &err_ty)));

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
			Err(found) => self.pos.error(TypeMis(&self.binding.typ, &found))
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
			Expr::NumLit(_, _) => match *expected_ty {
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

		// Fill in the gaps of `expected_ty` using own type ascription, if any
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
			|it| it.map(|(k, v)| (
				k,
				v.expect(&format!("AST::infer_types: const def `{}` is None", k)))));

		const_defs.do_for_item_at_height("main", 0, |const_defs, main| 
			main.infer_types(&Type::new_proc(vec![], Type::nil()), &mut Vec::new(), const_defs));
	}
}
