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

use std::{ fmt, mem };
use std::str::FromStr;
use std::collections::HashMap;
use llvm::*;
use lib::front::SrcPos;
use lib::front::parse::{ self, ExprMeta, Expr, StrLit, Path, SExpr, Block, If, Lambda };
use lib::collections::ScopeStack;
use self::CodegenErr::*;

enum CodegenErr {
	NumParseErr(String),
	ICE(String),
}
impl CodegenErr {
	fn num_parse_err<T: fmt::Display>(s: T) -> CodegenErr {
		NumParseErr(format!("{}", s))
	}
}
impl fmt::Display for CodegenErr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			NumParseErr(ref parse_as) =>
				write!(f, "Could not parse numeric literal as {}", parse_as),
			ICE(ref s) => write!(f, "Internal compiler error: {}", s),
		}
	}
}

pub struct Env<'src: 'cdef, 'cdef, 'ctx> {
	funcs: ScopeStack<&'src str, &'ctx Function>,
	consts: ScopeStack<&'src str, (&'ctx Value, &'cdef ExprMeta<'src>)>,
	vars: Vec<(&'src str, &'ctx Value)>,
}
impl<'src: 'cdef, 'cdef, 'ctx> Env<'src, 'cdef, 'ctx> {
	pub fn new() -> Self {
		Env {
			funcs: ScopeStack::new(),
			consts: ScopeStack::new(),
			vars: Vec::new(),
		}
	}
}

/// A codegenerator that visits all nodes in the AST, wherein it builds expressions
pub struct CodeGenerator<'ctx> {
	context: &'ctx Context,
	pub module: CSemiBox<'ctx, Module>,
	builder: CSemiBox<'ctx, Builder>,
}
impl<'src: 'cdef, 'cdef, 'ctx> CodeGenerator<'ctx> {
	pub fn new(context: &'ctx Context) -> Self {
		CodeGenerator {
			context: context,
			module: Module::new("main", context),
			builder: Builder::new(context),
		}
	}

	pub fn add_core_defs(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>) {
		let mut core_funcs = HashMap::new();

		let i64_t = Type::get::<i64>(self.context);
		let bool_t = Type::get::<bool>(self.context);

		for (unop, instr, in_typ, out_typ) in vec![
			("not", Builder::build_not, bool_t, bool_t),
		] {
			let func_typ = Type::new_function(in_typ, &[out_typ]);
			let func = &*self.module.add_function(unop, func_typ);
			let entry = func.append("entry");

			self.builder.position_at_end(entry);
			let operation = instr(&self.builder, &func[0]);
			self.builder.build_ret(operation);

			core_funcs.insert(unop, func);
		}

		for (binop, instr, a_typ, b_typ, out_typ) in vec![
			("+", Builder::build_add as fn (_, _, _) -> _, i64_t, i64_t, i64_t),
			("-", Builder::build_sub, i64_t, i64_t, i64_t),
			("*", Builder::build_mul, i64_t, i64_t, i64_t),
			("/", Builder::build_div, i64_t, i64_t, i64_t),
			("<<", Builder::build_shl, i64_t, i64_t, i64_t),
			(">>", Builder::build_ashr, i64_t, i64_t, i64_t),
			("and", Builder::build_and, bool_t, bool_t, bool_t),
			("or", Builder::build_or, bool_t, bool_t, bool_t),
			("xor", Builder::build_xor, bool_t, bool_t, bool_t),
		] {
			let func_typ = Type::new_function(out_typ, &[a_typ, b_typ]);
			let func = self.module.add_function(binop, func_typ);
			let entry = func.append("entry");

			self.builder.position_at_end(entry);
			let operation = instr(&self.builder, &func[0], &func[1]);
			self.builder.build_ret(operation);

			core_funcs.insert(binop, func);
		}

		for (id, predicate) in vec![
			("=", Predicate::Equal),
			("/=", Predicate::NotEqual),
			(">", Predicate::GreaterThan),
			(">=", Predicate::GreaterThanOrEqual),
			("<", Predicate::LessThan),
			("<=", Predicate::LessThanOrEqual),
		] {
			let func_typ = Type::new_function(bool_t, &[i64_t, i64_t]);
			let func = self.module.add_function(id, func_typ);
			let entry = func.append("entry");

			self.builder.position_at_end(entry);
			let r = self.builder.build_cmp(&func[0], &func[1], predicate);
			self.builder.build_ret(r);

			core_funcs.insert(id, func);
		}

		env.funcs.push(core_funcs);
	}

	fn current_func<'builder>(&'builder self) -> Option<&'builder Function> {
		self.builder.get_insert_block().and_then(|bb| bb.get_parent()).and_then(CastFrom::cast)
	}

	fn gen_nil(&self) -> &'ctx Value {
		Value::new_struct(self.context, &[], false)
	}

	fn gen_type(&self, typ: &parse::Type<'src>, pos: &SrcPos<'src>) -> &'ctx Type {
		use lib::front::parse::Type as PType;

		match *typ {
			PType::Unknown => pos.error(ICE("type was unknown at IR translation time".into())),
			PType::Basic("Int8") => Type::get::<i8>(self.context),
			PType::Basic("Int16") => Type::get::<i16>(self.context),
			PType::Basic("Int32") => Type::get::<i32>(self.context),
			PType::Basic("Int64") => Type::get::<i64>(self.context),
			PType::Basic("UInt8") => Type::get::<u8>(self.context),
			PType::Basic("UInt16") => Type::get::<u16>(self.context),
			PType::Basic("UInt32") => Type::get::<u32>(self.context),
			PType::Basic("UInt64") => Type::get::<u64>(self.context),
			PType::Basic("Bool") => Type::get::<bool>(self.context),
			PType::Basic("Float32") => Type::get::<f32>(self.context),
			PType::Basic("Float64") => Type::get::<f64>(self.context),
			PType::Basic("Nil") => Type::new_struct(&[], false),
			_ => unimplemented!(),
		}
	}

	fn gen_lit<I>(&self, lit: &str, typ: &parse::Type<'src>, pos: &SrcPos<'src>) -> &'ctx Value
		where I: Compile<'ctx> + FromStr
	{
		lit.parse::<I>()
			.map(|n| n.compile(self.context))
			.unwrap_or_else(|_| pos.error(CodegenErr::num_parse_err(typ)))
	}

	fn gen_num(&self, lit: &str, typ: &parse::Type<'src>, pos: &SrcPos<'src>) -> &'ctx Value {
		use lib::front::parse::Type as PType;

		let parser = match *typ {
			PType::Basic("Int8") => CodeGenerator::gen_lit::<i8>,
			PType::Basic("Int16") => CodeGenerator::gen_lit::<i16>,
			PType::Basic("Int32") => CodeGenerator::gen_lit::<i32>,
			PType::Basic("Int64") => CodeGenerator::gen_lit::<i64>,
			PType::Basic("IntPtr") => CodeGenerator::gen_lit::<isize>,
			PType::Basic("UInt8") => CodeGenerator::gen_lit::<u8>,
			PType::Basic("UInt16") => CodeGenerator::gen_lit::<u16>,
			PType::Basic("UInt32") => CodeGenerator::gen_lit::<u32>,
			PType::Basic("UInt64") => CodeGenerator::gen_lit::<u64>,
			PType::Basic("UIntPtr") => CodeGenerator::gen_lit::<usize>,
			PType::Basic("Bool") => CodeGenerator::gen_lit::<bool>,
			PType::Basic("Float32") => CodeGenerator::gen_lit::<f32>,
			PType::Basic("Float64") => CodeGenerator::gen_lit::<f64>,
			_ => pos.error(ICE("type of numeric literal is not numeric".into())),
		};
		parser(self, lit, typ, pos)
	}

	/// Gets an array, `[N x TYPE]`, as a pointer to the first element, `TYPE*`
	fn get_array_as_ptr(&self, array_ptr: &Value) -> &Value {
		// First, deref ptr to array (index first element of ptr, like pointer indexing in C).
		// Second, get address of first element in array == address of array start
		self.builder.build_gep(array_ptr, &vec![0usize.compile(self.context); 2])
	}

	fn gen_str(&self, lit: StrLit<'src>, pos: &SrcPos<'src>) -> &Value {
		let unescaped_lit = lit.unescape()
			.unwrap_or_else(|(e, i)| pos.with_positive_offset(i).error(e));

		let bytes = unescaped_lit.compile(self.context);

		let static_array = self.module.add_global_constant("str_lit", bytes);

		// A string literal is represented as a struct with a pointer to the byte array and the size
		// { i8* @lit.bytes, i64 /* machines ptr size */ 13 }
		//     where @lit.bytes = global [13 x i8] c"Hello, world!"
		Value::new_struct(
			self.context,
			&[self.get_array_as_ptr(static_array), unescaped_lit.len().compile(self.context)],
			false)
	}

	/// Generate IR for a binding used as an r-value
	fn gen_r_binding(&self, env: &mut Env<'src, 'cdef, 'ctx>, path: &Path<'src>) -> &Value {
		let binding = path.ident().expect("path was not ident");

		// Function pointers are returned as-is,
		// while static constants and variables are loaded into registers
		env.consts.get(binding)
			.map(|&(ptr, _)| ptr)
			.or(env.vars.iter()
				.rev()
				.find(|&&(id, _)| id == binding)
				.map(|&(_, ptr)| ptr))
			.map(|ptr| {
				let v = self.builder.build_load(ptr);
				v.set_name(&format!("{}_tmp", binding));
				v
			})
			.or(env.funcs.get(binding)
				.map(|&func| &**func))
		.unwrap_or_else(|| path.pos.error(ICE("undefined binding".into())))
	}

	/// Generates IR code for a procedure call. If the call is in a tail position and the call
	/// is a recursive call to the caller itself, make a tail call and return `Nothing`.
	/// Otherwise, make a normal call and return the result.
	fn gen_sexpr(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		sexpr: &'cdef SExpr<'src>,
		in_tail_pos: bool
	) -> Option<&Value> {
		let proced: &Function = self.gen_expr(env, &sexpr.proced, false)
			.map(CastFrom::cast)
			.unwrap()
			.unwrap_or_else(|| sexpr.proced.pos()
				.error(ICE("expression in procedure pos is not a function".into())));

		let mut args = Vec::new();
		for arg in &sexpr.args {
			args.push(self.gen_expr(env, arg, false).unwrap())
		}

		if in_tail_pos && proced == self.current_func().unwrap() {
			self.builder.build_tail_call(proced, &args);
			None
		} else {
			let call = self.builder.build_call(proced, &args);
			call.set_name("result");
			Some(call)
		}
	}

	fn gen_block(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		block: &'cdef Block<'src>,
		in_tail_pos: bool
	) -> Option<&Value> {
		self.gen_const_defs(env, &block.const_defs);

		let old_n_vars = env.vars.len();

		let (last, statements) = block.exprs.split_last().expect("no exprs in block");

		for statement in statements {
			self.gen_expr(env, statement, false);
		}

		let r = self.gen_expr(env, last, in_tail_pos);

		env.vars.truncate(old_n_vars);
		env.funcs.pop();
		env.consts.pop();

		r
	}

	fn gen_if(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		cond: &'cdef If<'src>,
		typ: &parse::Type<'src>,
		in_tail_pos: bool
	) -> Option<&Value> {
		let parent_func = self.current_func().unwrap();

		let then_br = parent_func.append("cond_then");
		let else_br = parent_func.append("cond_else");
		let next_br = parent_func.append("cond_next");

		self.builder.build_cond_br(
			self.gen_expr(env, &cond.predicate, false).unwrap(),
			then_br,
			Some(else_br));

		let mut phi_nodes = vec![];

		self.builder.position_at_end(then_br);
		if let Some(then_val) = self.gen_expr(env, &cond.consequent, in_tail_pos) {
			phi_nodes.push((then_val, then_br));
			self.builder.build_br(next_br);
		}

		self.builder.position_at_end(else_br);
		if let Some(else_val) = self.gen_expr(env, &cond.alternative, in_tail_pos) {
			phi_nodes.push((else_val, else_br));
			self.builder.build_br(next_br);
		}

		self.builder.position_at_end(next_br);
		if phi_nodes.is_empty() {
			None
		} else {
			Some(self.builder.build_phi(self.gen_type(typ, &cond.pos), &phi_nodes))
		}
	}

	fn gen_lambda(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>, lam: &'cdef Lambda<'src>)
		-> &Value
	{
		let anon = self.gen_func_decl("lambda", lam);

		self.build_func_def(env, anon, lam);

		anon
	}

	/// Generate llvm code for an expression and return its llvm Value.
	/// Returns `None` if the expression makes a tail call
	fn gen_expr(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		expr: &'cdef ExprMeta<'src>,
		in_tail_pos: bool
	) -> Option<&Value> {
		match *expr.val {
			Expr::Nil(_) => Some(self.gen_nil()),
			Expr::NumLit(lit, ref pos) => Some(self.gen_num(lit, &expr.typ, pos)),
			Expr::StrLit(lit, ref pos) => Some(self.gen_str(lit, pos)),
			Expr::Bool(b, _) => Some(b.compile(self.context)),
			Expr::Binding(ref path) => Some(self.gen_r_binding(env, path)),
			Expr::SExpr(ref sexpr) => self.gen_sexpr(env, sexpr, in_tail_pos),
			Expr::Block(ref block) => self.gen_block(env, block, in_tail_pos),
			Expr::If(ref cond) => self.gen_if(env, cond, &expr.typ, in_tail_pos),
			Expr::Lambda(ref lam) => Some(self.gen_lambda(env, lam)),
			Expr::VarDef(_) => unimplemented!(),
			Expr::Assign(_) => unimplemented!(),
			Expr::Symbol(_, _) => unimplemented!(),
		}
	}

	fn gen_eval_const_binding(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>, path: &Path<'src>)
		-> &Value
	{
		let binding = path.ident().expect("path was not ident");

		env.consts.get(binding)
			.cloned()
			.map(|(_, e)| self.gen_const_expr(env, e))
			.unwrap_or_else(|| path.pos.error("binding does not point to constant"))
	}


	fn gen_const_sexpr(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>, sexpr: &'cdef SExpr<'src>)
		-> &Value
	{
		let args = sexpr.args.iter()
			.map(|arg| self.gen_const_expr(env, arg))
			.collect::<Vec<_>>();

		match *sexpr.proced.val {
			Expr::Binding(ref path) if path == "+" =>
				self.builder.build_add(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "-" =>
				self.builder.build_sub(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "*" =>
				self.builder.build_mul(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "/" =>
				self.builder.build_div(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "and" =>
				self.builder.build_and(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "or" =>
				self.builder.build_or(&args[0], &args[1]),
			Expr::Binding(ref path) if path == "=" =>
				self.builder.build_cmp(&args[0], &args[1], Predicate::Equal),
			Expr::Binding(ref path) if path == ">" =>
				self.builder.build_cmp(&args[0], &args[1], Predicate::GreaterThan),
			Expr::Binding(ref path) if path == "<" =>
				self.builder.build_cmp(&args[0], &args[1], Predicate::LessThan),
			Expr::Binding(ref path) =>
				path.pos.error("Binding does not point to a constant function"),
			_ => sexpr.pos.error("Non-constant function in constant expression")
		}
	}

	fn gen_const_expr(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>, expr: &'cdef ExprMeta<'src>)
		-> &Value
	{
		// TODO: add internal eval over ExprMetas
		match *expr.val {
			Expr::Nil(_) => self.gen_nil(),
			Expr::NumLit(lit, ref pos) => self.gen_num(lit, &expr.typ, pos),
			Expr::StrLit(lit, ref pos) => self.gen_str(lit, pos),
			Expr::Bool(b, _) => b.compile(self.context),
			Expr::Binding(ref path) => self.gen_eval_const_binding(env, path),
			Expr::SExpr(ref sexpr) => self.gen_const_sexpr(env, sexpr),
			_ => expr.pos().error("expression cannot be used in a constant expression"),
		}
	}

	fn gen_const(&'ctx self, env: &mut Env<'src, 'cdef, 'ctx>, id: &str, def: &'cdef ExprMeta<'src>)
		-> &Value
	{
		self.module.add_global_constant(id, self.gen_const_expr(env, def))
	}

	fn gen_func_decl(&self, id: &str, lam: &Lambda<'src>) -> &mut Function {
		let typ = Type::new_function(
			self.gen_type(&lam.body.typ, lam.body.pos()),
			&lam.params.iter().map(|tb| self.gen_type(&tb.typ, &tb.pos)).collect::<Vec<_>>());

		let f = self.module.add_function(id, typ);

		for (i, param_name) in lam.params.iter().map(|tb| tb.ident).enumerate() {
			f[i].set_name(param_name)
		}

		f
	}

	fn build_func_def(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		func: &'ctx Function,
		def_lam: &'cdef Lambda<'src>
	) {
		let entry = func.append("entry");

		self.builder.position_at_end(entry);

		let params = def_lam.params.iter()
			.map(|tb| tb.ident)
			.enumerate()
			.map(|(i, id)| (id, &*func[i]))
			.collect::<Vec<_>>();

		let old_vars = mem::replace(&mut env.vars, params);
		if let Some(e) = self.gen_expr(env, &def_lam.body, true) {
			self.builder.build_ret(e);
		}

		env.vars = old_vars;
	}

	pub fn gen_const_defs(&'ctx self,
		env: &mut Env<'src, 'cdef, 'ctx>,
		const_defs: &'cdef HashMap<&'src str, parse::ConstDef<'src>>
	) {
		let (mut func_decls, mut const_decls) = (HashMap::new(), HashMap::new());
		// function declarations that are to be defined
		let (mut undef_funcs, mut undef_consts) = (Vec::new(), Vec::new());

		for (&id, const_def) in const_defs.iter() {
			match *const_def.body.val {
				Expr::Lambda(ref lam) => {
					let func: &_ = self.gen_func_decl(id, lam);
					func_decls.insert(id, func);
					undef_funcs.push((func, lam));
				},
				_ => {
					// temporarily set const definitions as undefined in order to have them all
					// available while generating the definition for each one
					const_decls.insert(
						id,
						(Value::new_undef(Type::get::<()>(self.context)), &const_def.body));
					undef_consts.push(id);
				},
			}
		}

		env.consts.push(const_decls);

		for id in undef_consts {
			let def = env.consts.get(id).unwrap().1;
			let const_val = self.gen_const(env, id, def);
			let undef = &mut env.consts.get_mut(id).unwrap().0;

			*undef = const_val;
		}

		env.funcs.push(func_decls);

		for (func, def_lam) in undef_funcs {
			self.build_func_def(env, func, def_lam);
		}
	}
}
