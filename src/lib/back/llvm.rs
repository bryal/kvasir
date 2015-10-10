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

use std::fmt::*;
use std::ffi::CString;
use std::slice;
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use llvm_sys::analysis::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use libc::c_ulonglong;
use ffi::*;
use self::CodegenErr::*;

enum CodegenErr<'p, 'src: 'p> {
	NumParseErr(&'static str),
	ICE(String),
}
impl<'src, 'p> fmt::Display for CodegenErr<'src, 'p> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			NumParseErr(parse_as) =>
				write!(f, "Could not parse numeric literal as {}", parse_as),
			ICE(s) => write!(f, "Internal compiler error: {}", s),
		}
	}
}

impl<'src> Type<'src> {
	fn llvm_type(&self) -> Option<LLVMTypeRef> {
		if let &Type::Unknown == self {
			return None;
		}
		Some(match *self {
			Type::Basic("Int8") => LLVMInt8Type(),
			Type::Basic("Int16") => LLVMInt16Type(),
			Type::Basic("Int32") => LLVMInt32Type(),
			Type::Basic("Int64") => LLVMInt64Type(),
			Type::Basic("UInt8") => LLVMInt8Type(),
			Type::Basic("UInt16") => LLVMInt16Type(),
			Type::Basic("UInt32") => LLVMInt32Type(),
			Type::Basic("UInt64") => LLVMInt64Type(),
			Type::Basic("Bool") => LLVMInt1Type(),
			Type::Basic("Float32") => LLVMFloatType(),
			Type::Basic("Float64") => LLVMDoubleType(),
			_ => unimplemented!(),
		})
	}
}

fn nil() -> LLVMValueRef { LLVMConstStruct(ptr::null_mut(), 0, 0) }


impl<'src> Path<'src> {
	fn llvm_codegen(&self, vars: HashMap<&str, LLVMValueRef>) {
		vars[self.ident().unwrap_or_else(|| unimplemented!())]
	}
}

impl<'src> SExpr<'src> {
	fn llvm_codegen(&self, module: LLVMModuleRef, builder: LLVMBuilderRef) -> LLVMValueRef {
		let proc_name = self.proc.as_binding()
			.and_then(|path| path.ident())
			.unwrap_or_else(|| unimplemented!());

		let c_proc_name = CString::new(proc_name).unwrap();
		
		let proc = LLVMGetNamedFunction(module, c_proc_name.as_ptr());

		let n_args = LLVMCountParams(proc);
		if n_args != self.args.len() {
			self.pos.error(ICE(format!("arity mismatch for {}. {} != {}",
				proc_name,
				n_args,
				self.args.len())))
		}

		let args = self.args.iter().map(|arg| arg.llvm_codegen());

		LLVMBuildCall(builder, proc, args.as_mut_ptr(), n_args, c_proc_name.as_ptr())
	}
} 

impl<'src> ExprMeta<'src> {
	fn llvm_codegen(&self) -> LLVMValueRef {
		match *self.val {
			Expr::Nil(_) => nil(),
			Expr::Assign(_) => unimplemented!();,
			Expr::NumLit(lit, ref pos) => num_lit_llvm_codegen(pos, lit, &self.typ),
			Expr::StrLit(_, _) => unimplemented!(), 
			Expr::Bool(b, ref pos) => LLVMConstInt(LLVMInt1Type(), b as c_ulonglong, 0),
			Expr::Binding(ref path) => path.llvm_codegen(),
			Expr::SExpr(ref sexpr) => sexpr.llvm_codegen(),
			Expr::Block(ref block) => unimplemented!(),
			Expr::Cond(ref mut cond) => unimplemented!(),
			Expr::Lambda(ref lambda) => unimplemented!(),
			Expr::Symbol(_, _) => unimplemented!(),
}

fn const_codegen(module: LLVMModuleRef, id: &str, val: ConstDef) {
	match *val.body.val {
		Expr::Lambda(ref lam) => function_codegen(module, ),
		Expr::NumLit(lit, ref pos) => val.body.codegen
	}
}

struct CodeGenerator<'src> {
	module: LLVMModuleRef,
	builder: LLVMBuilderRef,
	const_defs: ScopeStack<&'src str, LLVMValueRef>,
	vars: Vec<(&'src str, LLVMValueRef)>,
}
impl<'src> CodeGenerator<'src> {
	fn gen_func_decl(&self, id: &'src str, lam: &Lambda) -> LLVMValueRef {
		let typ = LLVMFunctionType(
			self.gen_typ(&lam.body.typ),
			lam.params.iter().map(|tb| self.gen_typ(&tb.typ)).collect().as_mut_ptr(),
			lam.params.len(),
			0);
		let f = LLVMAddFunction(self.module, CString::new(id).unwrap().as_ptr(), typ);

		for (i, param_name) in lambda.params.iter()
			.map(|param| CString::new(param.ident))
			.enumerate()
		{
			LLVMSetValueName(LLVMGetParam(f, i), param_name.as_ptr());
		}
		f
	}

	fn build_func_def(&mut self, func: LLVMValueRef, def_lam: &Lambda) {
		let entry = LLVMAppendBasicBlock(func, b"entry\0".as_ptr());

		LLVMBuilderAtEnd(self.builder, entry);

		let mut params = vec![ptr::null_mut(): LLVMCountParams()];
		LLVMGetParams(func, params.as_mut_ptr());

		let old_n_vars = self.vars.len();
		self.vars.extend(params);
		
		LLVMBuildRet(self.builder, self.gen_expr(&def_lam.body));

		self.vars.shrink(old_n_vars)
	}

	fn gen_const(&self, id: &str, def: &ConstDef) -> LLVMValueRef {
		match *def.body.val {
			Expr::NumLit(lit, ref pos) => 
}
	}
}

pub fn codegen(ast: &AST) -> LLVMValueRef {
	let mut codegenerator = CodeGenerator {
		module: LLVMModuleCreateWithName(b"main\0".as_ptr()),
		builder: LLVMCreateBuilder(),
		const_defs: Vec::new(),
	};

	let (mut glob_funcs, mut glob_consts) = (Vec::new(), Vec::new());

	for &(id, ref const_def) in ast.const_defs.iter() {
		match *const_def.body.val {
			Expr::Lambda(ref lam) => glob_func.push(
				(lam, codegenerator.gen_func_decl(id, lam))),
			ref e => glob_consts.push(codegenerator.gen_const(e)),
		}
	}

	codegenerator.const_defs.push(
		glob_funcs.iter()
			.map(|&(_, decl)| decl)
			.collect());

	for (def_lam, func_decl) in glob_funcs {
		codegenerator.build_func_def(func_decl, def_lam);
	}
}
