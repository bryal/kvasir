
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
use std::mem::replace;
use std::collections::HashMap;
use lib::front::ast::*;
use lib::collections::ScopeStack;
use self::InferenceErr::*;

enum InferenceErr<'p, 'src: 'p> {
	/// Type mismatch. (expected, found)
	TypeMis(&'p Type<'src>, &'p Type<'src>),
	ArmsDiffer(&'p Type<'src>, &'p Type<'src>),
}
impl<'src, 'p> Display for InferenceErr<'src, 'p> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			TypeMis(expected, found) =>
				write!(f, "Type mismatch. Expected `{}`, found `{}`", expected, found),
			ArmsDiffer(c, a) =>
				write!(f, "Consequent and alternative have different types. \
				           Expected `{}` from alternative, found `{}`",
					c,
					a),
		}
	}
}

struct Inferer<'src> {
	vars: Vec<(Ident<'src>, Type<'src>)>,
	const_defs: ScopeStack<Ident<'src>, Option<ConstDef<'src>>>,
	extern_funcs: ScopeStack<Ident<'src>, Type<'src>>,
}
impl<'src> Inferer<'src> {
	fn new(ast: &mut AST<'src>) -> Self {
		let mut const_defs = ScopeStack::new();
		const_defs.push(
			replace(&mut ast.const_defs, HashMap::new())
				.into_iter()
				.map(|(k, v)| (k, Some(v)))
				.collect());

		let mut extern_funcs = ScopeStack::new();
		extern_funcs.push(replace(&mut ast.extern_funcs, HashMap::new()));

		Inferer {
			vars: Vec::new(),
			const_defs: const_defs,
			extern_funcs: extern_funcs,
		}
	}

	fn into_inner(mut self)
		-> (HashMap<Ident<'src>, ConstDef<'src>>, HashMap<Ident<'src>, Type<'src>>)
	{
		let const_defs = self.const_defs.pop()
			.expect("ICE: Inferer::into_inner: const_defs.pop() failed")
			.into_iter()
			.map(|(k, v)| (k, v.expect("ICE: Inferer::into_inner: None when unmapping const def")))
			.collect();
		let extern_funcs = self.extern_funcs.pop()
			.expect("ICE: Inferer::into_inner: extern_funcs.pop() failed");

		(const_defs, extern_funcs)
	}

	fn get_var_type(&self, id: &str) -> Option<&Type<'src>> {
		self.vars.iter().rev().find(|&&(ref b, _)| b == id).map(|&(_, ref t)| t)
	}

	fn get_var_type_mut(&mut self, id: &str) -> Option<&mut Type<'src>> {
		self.vars.iter_mut().rev().find(|&&mut (ref b, _)| b == id).map(|&mut (_, ref mut t)| t)
	}

	fn infer_const_def(&mut self, def: &mut ConstDef<'src>, expected_ty: &Type<'src>)
		-> Type<'src>
	{
		self.infer_expr_meta(&mut def.body, expected_ty)
			.unwrap_or_else(|found_ty| def.body.pos().error(TypeMis(expected_ty, &found_ty)))
	}

	fn infer_path(&mut self, path: &Path<'src>, expected_ty: &Type<'src>)
		-> Result<Type<'src>, Type<'src>>
	{
		let ident = if let Some(ident) = path.ident() {
			ident
		} else {
			panic!("Inferer::infer_path: Not implemented for anything but basic identifiers")
		};

		// In order to not violate any borrowing rules, use get_height to check if entry exists
		// and to speed up upcoming lookup
		if let Some(height) = self.extern_funcs.get_height(ident) {
			// Don't infer types for external items,
			// just check compatibility with expected_ty

			let typ = self.extern_funcs.get_at_height(ident, height).unwrap();
			typ.infer_by(expected_ty).ok_or(typ.clone())
		} else if let Some(height) = self.const_defs.get_height(ident) {
			// Path is a constant

			let maybe_def = replace(
				self.const_defs.get_at_height_mut(ident, height).unwrap(),
				None);

			if let Some(mut def) = maybe_def {
				let old_vars = replace(&mut self.vars, Vec::new());

				let infered = self.infer_const_def(&mut def, expected_ty);

				self.vars = old_vars;
				self.const_defs.update(ident, Some(def));

				Ok(infered)
			} else {
				// We are currently doing inference inside this definition

				Ok(Type::Unknown)
			}
		} else if let Some(stack_bnd_ty) = self.get_var_type_mut(ident) {
			// Path is a var

			stack_bnd_ty.infer_by(expected_ty)
				.map(|inferred| {
					*stack_bnd_ty = inferred.clone();
					inferred
				})
				.ok_or(stack_bnd_ty.clone())
		} else {
			path.pos.error(format!("Unresolved path `{}`", ident))
		}
	}

	fn infer_call_arg_types(&mut self, call: &mut Call<'src>)  {
		let expected_types: Vec<&Type> = if call.proced.typ.is_partially_known() {
			// The type of the procedure is not unknown.
			// If it's a valid procedure type, use it for inference

			match call.proced.typ.get_proc_sig() {
				Some((param_tys, _)) if param_tys.len() == call.args.len() =>
					param_tys.iter().collect(),
				Some((param_tys, _)) => call.pos.error(
					format!("Arity mismatch. Expected {}, found {}",
						param_tys.len(),
						call.args.len())),
				None => call.proced.pos().error(
					TypeMis(
						&Type::new_proc(vec![Type::Unknown], Type::Unknown),
						&call.proced.typ)),
			}
		} else {
			vec![&call.proced.typ; call.args.len()]
		};

		for (arg, expect_ty) in call.args.iter_mut().zip(expected_types) {
			if let Err(ref err_ty) = self.infer_expr_meta(arg, expect_ty) {
				arg.pos().error(TypeMis(expect_ty, err_ty));
			}
		}
	}

	fn infer_call<'call>(&mut self, call: &'call mut Call<'src>, expected_ty: &Type<'src>)
		-> &'call Type<'src>
	{
		self.infer_call_arg_types(call);

		let expected_proc_type = Type::new_proc(
			call.args.iter().map(|tb| tb.typ.clone()).collect(),
			expected_ty.clone());

		if let Err(err_ty) = self.infer_expr_meta(&mut call.proced, &expected_proc_type) {
			call.proced.pos().error(TypeMis(&expected_proc_type, &err_ty));
		}

		// TODO: This only works for function pointers, i.e. lambdas will need some different type.
		//       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

		if call.proced.typ.is_partially_known() {
			// If type of the calls procedure hasn't been infered,
			// there's no new data to help with infence
			self.infer_call_arg_types(call);
		}

		call.body_type()
	}

	fn infer_block(&mut self, block: &mut Block<'src>, expected_ty: &Type<'src>) -> Type<'src> {
		let (init, last) = if let Some((last, init)) = block.exprs.split_last_mut() {
			if last.val.is_var_def() {
				last.pos().error("Block ended with variable definition");
			}
			(init, last)
		} else {
			return Type::nil()
		};

		self.const_defs.push(
			replace(&mut block.const_defs, HashMap::new())
				.into_iter()
				.map(|(k, v)| (k, Some(v)))
				.collect());

		let old_vars_len = self.vars.len();

		// First pass. If possible, all vars defined in block should have types infered.
		for expr in init.iter_mut() {
			if let Expr::VarDef(ref mut var_def) = *expr.val {
				self.infer_var_def(var_def);
				self.vars.push((var_def.binding.clone(), var_def.get_type().clone()));
			} else {
				self.infer_expr_meta(expr, &Type::Unknown)
					.expect("ICE: error infering expr in block");
			}
		}

		self.infer_expr_meta(last, expected_ty)
			.unwrap_or_else(|err_ty| last.pos().error(TypeMis(expected_ty, &err_ty)));

		let mut block_defined_vars = self.vars.split_off(old_vars_len).into_iter();

		// Second pass. Infer types for all expressions in block now that types for all bindings
		// are, if possible, known.
		for expr in init {
			if let Expr::VarDef(ref mut var_def) = *expr.val {
				let v = block_defined_vars.next().expect("ICE: block_defined_vars empty");

				self.infer_expr_meta(&mut var_def.body, &v.1);

				self.vars.push(v);
			} else {
				self.infer_expr_meta(expr, &Type::Unknown)
					.unwrap_or_else(|err_ty| expr.pos().error(TypeMis(&Type::Unknown, &err_ty)));
			}
		}
		self.infer_expr_meta(last, expected_ty)
			.unwrap_or_else(|err_ty| last.pos().error(TypeMis(expected_ty, &err_ty)));

		self.vars.truncate(old_vars_len);

		block.const_defs = self.const_defs.pop()
			.expect("ICE: ScopeStack was empty when replacing Block const defs")
			.into_iter()
			.map(|(k, v)| (k, v.expect("ICE: None when unmapping block const def")))
			.collect();

		last.typ.clone()
	}

	fn infer_if(&mut self, cond: &mut If<'src>, expected_type: &Type<'src>)
		-> Result<Type<'src>, Type<'src>>
	{
		self.infer_expr_meta(&mut cond.predicate, &Type::Basic("Bool"))
			.unwrap_or_else(|err_ty|
				cond.predicate.pos().error(TypeMis(&Type::Basic("Bool"), &err_ty)));

		for clause in &mut [&mut cond.consequent, &mut cond.alternative] {
			self.infer_expr_meta(clause, expected_type)
				.unwrap_or_else(|err_ty|
					clause.pos().error(TypeMis(expected_type, &err_ty)));
		}

		if let Some(inferred) = cond.consequent.typ.infer_by(&cond.alternative.typ) {
			if cond.consequent.typ == inferred && cond.alternative.typ == inferred {
				Ok(inferred)
			} else {
				self.infer_if(cond, &inferred)
			}
		} else {
			cond.pos.error(ArmsDiffer(&cond.consequent.typ, &cond.alternative.typ))
		}
	}

	fn infer_lambda_args(&mut self, lam: &mut Lambda<'src>, expected_params: &[&Type<'src>]) {
		for (param, expected_param) in lam.params.iter_mut().zip(expected_params) {
			match param.typ.infer_by(expected_param) {
				Some(infered) => param.typ = infered,
				None => param.ident.pos.error(TypeMis(expected_param, &param.typ))
			}
		}
	}

	fn infer_lambda(&mut self, lam: &mut Lambda<'src>, expected_ty: &Type<'src>)
		-> Result<Type<'src>, Type<'src>>
	{
		let (expected_params, expected_body) = match expected_ty.get_proc_sig() {
			Some((params, _)) if params.len() != lam.params.len() => return Err(lam.get_type()),
			Some((params, body)) => (params.iter().collect(), body),
			None if *expected_ty == Type::Unknown => (
				vec![expected_ty; lam.params.len()],
				expected_ty,
			),
			None => return Err(lam.get_type()),
		};

		// Own type is `Unknown` if no type has been infered yet, or none was inferable

		if lam.get_type().is_partially_known() {
			if let Some(infered) = expected_ty.infer_by(&lam.get_type()) {
				if lam.get_type() == infered {
					// Own type can't be infered further by `expected_ty`
					return Ok(lam.get_type());
				}
			} else {
				// Own type and expected type are not compatible. Type mismatch
				return Err(lam.get_type());
			}
		}

		self.infer_lambda_args(lam, &expected_params);

		let (vars_len, n_params) = (self.vars.len(), lam.params.len());

		self.vars.extend(lam.params.iter().cloned().map(|param| (param.ident, param.typ)));

		self.infer_expr_meta(&mut lam.body, &expected_body)
			.unwrap_or_else(|err_ty| lam.body.pos().error(TypeMis(expected_body, &err_ty)));

		assert_eq!(self.vars.len(), vars_len + n_params);

		for (param, found) in lam.params.iter_mut()
			.zip(self.vars.drain(vars_len..))
			.map(|(param, (_, found))| (&mut param.typ, found))
		{
			*param = found;
		}
		Ok(lam.get_type())
	}

	fn infer_var_def(&mut self, def: &mut VarDef<'src>) {
		self.infer_expr_meta(&mut def.body, &Type::Unknown)
			.expect("ICE: infer_var_def: infer_expr_meta returned Err");
	}

	/// On success, return expected, infered type. On failure, return unexpected, found type
	fn infer_expr(&mut self, expr: &mut Expr<'src>, expected_ty: &Type<'src>)
		-> Result<Type<'src>, Type<'src>>
	{
		match *expr {
			Expr::Nil(_) => expected_ty.infer_by(&Type::nil()).ok_or(Type::nil()),
			Expr::VarDef(ref mut def) => if expected_ty.infer_by(&Type::nil()).is_some() {
				self.infer_var_def(def);
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
			Expr::Binding(ref path) => self.infer_path(path, &expected_ty),
			Expr::Call(ref mut call) =>
				Ok(self.infer_call(call, &expected_ty).clone()),
			Expr::Block(ref mut block) =>
				Ok(self.infer_block(block, &expected_ty)),
			Expr::If(ref mut cond) => self.infer_if(cond, &expected_ty),
			Expr::Lambda(ref mut lam) => self.infer_lambda(lam, &expected_ty),
			Expr::Symbol(_) => expected_ty.infer_by(&Type::Basic("Symbol"))
				.ok_or(Type::Basic("Symbol")),
		}
	}

	/// On type mismatch, return mismatched, found type as `Err`.
	/// Otherwise, return type of `self` as `Ok`
	fn infer_expr_meta(&mut self, expr: &mut ExprMeta<'src>, expected_ty: &Type<'src>)
		-> Result<Type<'src>, Type<'src>>
	{
		// Own type is `Unknown` if no type has been infered yet, or none was inferable
		if expr.typ.is_partially_known() {
			if let Some(infered) = expected_ty.infer_by(&expr.typ) {
				if expr.typ == infered {
					// Own type can't be infered further by `expected_ty`
					return Ok(expr.typ.clone());
				}
			} else {
				// Own type and expected type are not compatible. Type mismatch
				return Err(expr.typ.clone());
			}
		}

		// Own type is unknown, or `expected_ty` is more known than own type

		// Fill in the gaps of `expected_ty` using own type ascription, if any
		let expected_ty = if let Some(ref ty_ascription) = expr.ty_ascription {
			match expected_ty.infer_by(&ty_ascription.0) {
				Some(infered) => infered,
				None => return Err(ty_ascription.0.clone()),
			}
		} else {
			expected_ty.clone()
		};

		let found_type = try!(self.infer_expr(&mut expr.val, &expected_ty));

		expr.typ = found_type.clone();
		Ok(found_type)
	}
}

pub fn infer_types(ast: &mut AST) {
	let mut inferer = Inferer::new(ast);

	let mut main = replace(
			inferer.const_defs.get_mut("main").expect("ICE: In infer_ast: No main def"),
			None)
		.unwrap();

	inferer.infer_const_def(
		&mut main,
		&Type::new_proc(vec![], Type::Basic("Int64")));

	inferer.const_defs.update("main", Some(main));

	let (const_defs, extern_funcs) = inferer.into_inner();

	ast.const_defs = const_defs;
	ast.extern_funcs = extern_funcs;
}
