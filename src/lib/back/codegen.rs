use lib::front::SrcPos;
use lib::front::ast::{self, Expr};
use llvm_sys;
use llvm_sys::prelude::*;
use llvm_sys::target::LLVMTargetDataRef;
use std::{fmt, mem, cmp};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::str::FromStr;
use std::iter::once;
use super::llvm::*;
use self::CodegenErr::*;

type Instantiations<'src> = BTreeSet<(Vec<ast::Type<'src>>, ast::Type<'src>)>;
type FreeVarInsts<'src> = BTreeMap<&'src str, Instantiations<'src>>;

fn val_nil(ctx: &Context) -> &Value {
    Value::new_struct(ctx, &[], false)
}

fn type_nil(ctx: &Context) -> &Type {
    StructType::new(ctx, &[], false)
}

fn type_generic_ptr(ctx: &Context) -> &Type {
    PointerType::new(Type::get::<u8>(ctx))
}

/// The type of a reference counted pointer to `contents`
///
/// `{i64, contents}*`
fn type_rc<'ctx>(ctx: &'ctx Context, contents: &'ctx Type) -> &'ctx Type {
    PointerType::new(StructType::new(
        ctx,
        &[Type::get::<u64>(ctx), contents],
        false,
    ))
}

/// A generic reference counted pointer.
///
/// A pointer to the 64-bit reference count integer, and an `i8` to represent the
/// following, variable sized contents
///
/// `{i64, i8}*`
fn type_rc_generic<'ctx>(ctx: &'ctx Context) -> &'ctx Type {
    type_rc(ctx, Type::get::<u8>(ctx))
}

/// Returns the unit set of the single element `x`
fn set_of<T: cmp::Ord>(x: T) -> BTreeSet<T> {
    once(x).collect()
}

/// Returns the map of `{k} -> {v}`
fn map_of<K: cmp::Ord, V>(k: K, v: V) -> BTreeMap<K, V> {
    once((k, v)).collect()
}

fn free_vars_in_exprs<'src>(es: &[&ast::Expr<'src>]) -> FreeVarInsts<'src> {
    let mut fvs = BTreeMap::new();
    for fvs2 in es.iter().map(|e2| free_vars_in_expr(e2)) {
        for (k, v) in fvs2 {
            fvs.entry(k).or_insert(BTreeSet::new()).extend(v)
        }
    }
    fvs
}

/// Returns a map of the free variables in `e`, where each variable name is mapped to the
/// instantiations of the free variable in `e`
fn free_vars_in_expr<'src>(e: &ast::Expr<'src>) -> FreeVarInsts<'src> {
    use self::ast::Expr::*;
    match *e {
        Nil(_) | NumLit(_) | StrLit(_) | Bool(_) => FreeVarInsts::new(),
        Variable(ref v) => {
            map_of(
                v.ident.s,
                set_of((
                    v.typ.get_inst_args().unwrap_or(&[]).to_vec(),
                    v.typ.clone(),
                )),
            )
        }
        App(box ref a) => free_vars_in_exprs(&[&a.func, &a.arg]),
        If(ref i) => free_vars_in_exprs(&[&i.predicate, &i.consequent, &i.alternative]),
        Lambda(box ref l) => free_vars_in_lambda(l),
        Let(box ref l) => {
            let mut es = vec![&l.body];
            es.extend(l.bindings.bindings().map(|b| &b.val));
            let mut fvs = free_vars_in_exprs(&es);
            for b in l.bindings.bindings() {
                fvs.remove(b.ident.s);
            }
            fvs
        }
        TypeAscript(_) => panic!("free_vars_in_expr encountered TypeAscript"),
        Cons(box ref c) => free_vars_in_exprs(&[&c.car, &c.cdr]),
    }
}

/// Returns a map of the free variables in `e`, where each variable name is mapped to the
/// instantiations of the free variable in `e`
fn free_vars_in_lambda<'src>(lam: &ast::Lambda<'src>) -> FreeVarInsts<'src> {
    let mut free_vars = free_vars_in_expr(&lam.body);
    free_vars.remove(lam.param_ident.s);
    free_vars
}

/// Get free variables of `lam`, but filter out externs
fn free_vars_in_lambda_filter_externs<'src, 'ctx>(
    env: &Env<'src, 'ctx>,
    lam: &ast::Lambda<'src>,
) -> FreeVarInsts<'src> {
    free_vars_in_lambda(&lam)
        .into_iter()
        .filter(|&(k, _)| env.vars.contains_key(k))
        .collect::<FreeVarInsts>()
}

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
            NumParseErr(ref parse_as) => {
                write!(f, "Could not parse numeric literal as {}", parse_as)
            }
            ICE(ref s) => write!(f, "Internal compiler error: {}", s),
        }
    }
}

enum Var<'ctx> {
    Func(&'ctx Function),
    Val(&'ctx Value),
}

#[derive(Debug)]
struct Env<'src, 'ctx> {
    externs: BTreeMap<&'src str, &'ctx Function>,
    vars: BTreeMap<&'src str, Vec<BTreeMap<Vec<ast::Type<'src>>, &'ctx Value>>>,
}

impl<'src, 'ctx> Env<'src, 'ctx> {
    fn new() -> Self {
        Env {
            externs: BTreeMap::new(),
            vars: BTreeMap::new(),
        }
    }

    fn get_var(&self, s: &str, ts: &[ast::Type]) -> Option<&'ctx Value> {
        self.vars
            .get(s)
            .and_then(|l| l.last())
            .and_then(|is| is.get(ts))
            .map(|&x| x)
    }

    fn get(&self, s: &str, ts: &[ast::Type]) -> Option<Var<'ctx>> {
        let val = self.get_var(s, ts).map(Var::Val);
        let ext = self.externs.get(s).map(|x| Var::Func(x));
        val.or(ext)
    }

    fn push_var(&mut self, id: &'src str, var: BTreeMap<Vec<ast::Type<'src>>, &'ctx Value>) {
        self.vars.entry(id).or_insert(Vec::new()).push(var)
    }

    fn add_inst(&mut self, id: &'src str, inst: Vec<ast::Type<'src>>, val: &'ctx Value) {
        let v = self.vars.entry(id).or_insert(Vec::new());
        if v.is_empty() {
            v.push(BTreeMap::new());
        }
        if v.last_mut().unwrap().insert(inst, val).is_some() {
            panic!("ICE: val already exists for inst")
        }
    }

    fn pop(&mut self, id: &str) -> BTreeMap<Vec<ast::Type<'src>>, &'ctx Value> {
        self.vars
            .get_mut(id)
            .expect("ICE: Var not in env")
            .pop()
            .expect("ICE: Popped empty `vars` of env")
    }
}

/// A codegenerator that visits all nodes in the AST, wherein it builds expressions
pub struct CodeGenerator<'ctx> {
    ctx: &'ctx Context,
    pub module: &'ctx Module,
    builder: &'ctx Builder,
    /// The function currently being built
    current_func: RefCell<Option<&'ctx Function>>,
    current_block: RefCell<Option<&'ctx BasicBlock>>,
}
impl<'src: 'ast, 'ast, 'ctx> CodeGenerator<'ctx> {
    pub fn new(ctx: &'ctx Context, builder: &'ctx Builder, module: &'ctx Module) -> Self {
        CodeGenerator {
            ctx: ctx,
            module: module,
            builder: builder,
            current_func: RefCell::new(None),
            current_block: RefCell::new(None),
        }
    }

    fn size_of(&self, t: &Type) -> u64 {
        unsafe {
            let module_ref = mem::transmute::<&Module, LLVMModuleRef>(self.module);
            let target_data_layout = mem::transmute::<LLVMTargetDataRef, &TargetData>(
                llvm_sys::target::LLVMGetModuleDataLayout(module_ref),
            );
            target_data_layout.size_of(t)
        }
    }

    fn gen_func_type(&self, arg: &ast::Type<'src>, ret: &ast::Type<'src>) -> &'ctx Type {
        FunctionType::new(
            self.gen_type(ret),
            &[type_generic_ptr(self.ctx), self.gen_type(arg)],
        )
    }

    fn gen_extern_func_type(&self, arg: &ast::Type<'src>, ret: &ast::Type<'src>) -> &'ctx Type {
        FunctionType::new(self.gen_type(ret), &[self.gen_type(arg)])
    }

    fn gen_type(&self, typ: &'ast ast::Type<'src>) -> &'ctx Type {
        use lib::front::ast::Type as PType;
        match *typ {
            PType::Var(_) => panic!("Type was Unknown at compile time"),
            PType::Const("Int8") => Type::get::<i8>(self.ctx),
            PType::Const("Int16") => Type::get::<i16>(self.ctx),
            PType::Const("Int32") => Type::get::<i32>(self.ctx),
            PType::Const("Int64") => Type::get::<i64>(self.ctx),
            PType::Const("Int") => Type::get::<isize>(self.ctx),
            PType::Const("UInt8") => Type::get::<u8>(self.ctx),
            PType::Const("UInt16") => Type::get::<u16>(self.ctx),
            PType::Const("UInt32") => Type::get::<u32>(self.ctx),
            PType::Const("UInt64") => Type::get::<u64>(self.ctx),
            PType::Const("UInt") => Type::get::<usize>(self.ctx),
            PType::Const("Bool") => Type::get::<bool>(self.ctx),
            PType::Const("Float32") => Type::get::<f32>(self.ctx),
            PType::Const("Float64") => Type::get::<f64>(self.ctx),
            PType::Const("Nil") => type_nil(self.ctx),
            PType::App(box ast::TypeFunc::Const(s), ref ts) => {
                match s {
                    "->" => {
                        let fp = PointerType::new(self.gen_func_type(&ts[0], &ts[1]));
                        let captures = type_rc_generic(self.ctx);
                        StructType::new(self.ctx, &[fp, captures], false)
                    }
                    "Cons" => {
                        StructType::new(
                            self.ctx,
                            &[self.gen_type(&ts[0]), self.gen_type(&ts[1])],
                            false,
                        )
                    }
                    "Ptr" => PointerType::new(self.gen_type(&ts[0])),
                    _ => panic!("ICE: Type function `{}` not implemented", s),
                }
            }
            _ => panic!("ICE: Type `{}` is not yet implemented", typ),
        }
    }

    /// Returns the type of the free variables when captured
    fn captures_type_of_free_vars(&self, free_vars: &FreeVarInsts<'src>) -> &'ctx Type {
        let mut captures_types = Vec::new();
        for (_, insts) in free_vars {
            for &(_, ref typ) in insts {
                captures_types.push(self.gen_type(typ));
            }
        }
        StructType::new(self.ctx, &captures_types, false)
    }

    fn gen_func_decl(&self, id: &str, typ: &ast::Type<'src>) -> &'ctx mut Function {
        let (arg, ret) = typ.get_func().expect(&format!(
            "ICE: Invalid function type `{}`",
            typ
        ));
        let func_typ = self.gen_func_type(arg, ret);
        self.module.add_function(id, func_typ)
    }

    fn gen_extern_func_decl(&self, id: &str, typ: &ast::Type<'src>) -> &'ctx mut Function {
        let (arg, ret) = typ.get_func().expect(&format!(
            "ICE: Invalid function type `{}`",
            typ
        ));
        let func_typ = self.gen_extern_func_type(arg, ret);
        self.module.add_function(id, func_typ)
    }

    fn gen_extern_decls(
        &self,
        env: &mut Env<'src, 'ctx>,
        externs: &BTreeMap<&'src str, ast::ExternDecl<'src>>,
    ) {
        for (id, decl) in externs.iter() {
            // TODO: External non-function variable declarations?
            if decl.typ.get_func().is_none() {
                decl.pos.error("Non-function externs not yet implemented");
                unimplemented!()
            }
            env.externs.insert(
                id,
                self.gen_extern_func_decl(id, &decl.typ) as &_,
            );
        }
    }

    fn parse_gen_lit<I>(&self, lit: &str, typ: &ast::Type<'src>, pos: &SrcPos<'src>) -> &'ctx Value
    where
        I: Compile<'ctx> + FromStr,
    {
        lit.parse::<I>()
            .map(|n| n.compile(self.ctx))
            .unwrap_or_else(|_| pos.error_exit(CodegenErr::num_parse_err(typ)))
    }

    fn gen_num(&self, num: &ast::NumLit) -> &'ctx Value {
        let parser = match num.typ {
            ast::Type::Const("Int8") => CodeGenerator::parse_gen_lit::<i8>,
            ast::Type::Const("Int16") => CodeGenerator::parse_gen_lit::<i16>,
            ast::Type::Const("Int32") => CodeGenerator::parse_gen_lit::<i32>,
            ast::Type::Const("Int64") => CodeGenerator::parse_gen_lit::<i64>,
            ast::Type::Const("Int") => CodeGenerator::parse_gen_lit::<isize>,
            ast::Type::Const("UInt8") => CodeGenerator::parse_gen_lit::<u8>,
            ast::Type::Const("UInt16") => CodeGenerator::parse_gen_lit::<u16>,
            ast::Type::Const("UInt32") => CodeGenerator::parse_gen_lit::<u32>,
            ast::Type::Const("UInt64") => CodeGenerator::parse_gen_lit::<u64>,
            ast::Type::Const("UInt") => CodeGenerator::parse_gen_lit::<usize>,
            ast::Type::Const("Bool") => CodeGenerator::parse_gen_lit::<bool>,
            ast::Type::Const("Float32") => CodeGenerator::parse_gen_lit::<f32>,
            ast::Type::Const("Float64") => CodeGenerator::parse_gen_lit::<f64>,
            _ => {
                num.pos.error_exit(
                    ICE("type of numeric literal is not numeric".into()),
                )
            }
        };
        parser(self, &num.lit, &num.typ, &num.pos)
    }

    fn gen_str(&self, _: &'ast ast::StrLit<'src>) -> &'ctx Value {
        unimplemented!()
    }

    /// Generate IR for a variable used as an r-value
    fn gen_variable(
        &self,
        env: &mut Env<'src, 'ctx>,
        var: &'ast ast::Variable<'src>,
    ) -> &'ctx Value {
        let inst = var.typ.get_inst_args().unwrap_or(&[]);
        match env.get(var.ident.s, inst) {
            Some(Var::Func(fp)) => {
                // Wrap function pointer in function+closure union
                let null_captures = null_byte_pointer(self.ctx);
                Value::new_struct(self.ctx, &[fp, null_captures], false)
            }
            Some(Var::Val(v)) => {
                println!("v: {:?}", v);
                v
            }
            // Undefined variables are caught during type check/inference
            None => unreachable!(),
        }
    }

    fn build_if<F, G>(
        &self,
        mut env: &mut Env<'src, 'ctx>,
        pred: &'ctx Value,
        cons: F,
        alt: G,
    ) -> &'ctx Value
    where
        F: FnOnce(&Self, &mut Env<'src, 'ctx>) -> &'ctx Value,
        G: FnOnce(&Self, &mut Env<'src, 'ctx>) -> &'ctx Value,
    {
        let parent_func = self.current_func.borrow().unwrap();
        let then_br = parent_func.append("cond_then");
        let else_br = parent_func.append("cond_else");
        let next_br = parent_func.append("cond_next");
        self.builder.build_cond_br(pred, then_br, else_br);
        let mut phi_nodes = vec![];
        self.builder.position_at_end(then_br);
        let then_val = cons(self, &mut env);
        phi_nodes.push((then_val, then_br));
        self.builder.build_br(next_br);
        self.builder.position_at_end(else_br);
        let else_val = alt(self, &mut env);
        phi_nodes.push((else_val, else_br));
        self.builder.build_br(next_br);
        self.builder.position_at_end(next_br);
        self.builder.build_phi(then_val.get_type(), &phi_nodes)
    }

    fn gen_if(&self, env: &mut Env<'src, 'ctx>, cond: &'ast ast::If<'src>) -> &'ctx Value {
        let pred = self.gen_expr(env, &cond.predicate, None);
        let cons = |generator: &Self, env: &mut Env<'src, 'ctx>| {
            generator.gen_expr(env, &cond.consequent, None)
        };
        let alt = |generator: &Self, env: &mut Env<'src, 'ctx>| {
            generator.gen_expr(env, &cond.alternative, None)
        };
        self.build_if(env, pred, cons, alt)
    }

    /// Build the application of a function to an argument
    fn build_app(
        &self,
        env: &mut Env<'src, 'ctx>,
        closure: &'ctx Value,
        (arg, arg_type): (&'ctx Value, &'ctx Type),
        ret_type: &'ctx Type,
    ) -> &'ctx Value {
        let func_ptr = self.builder.build_extract_value(closure, 0);
        let captures_rc = self.builder.build_extract_value(closure, 1);
        let captures_rc_int = self.builder.build_ptr_to_int(
            captures_rc,
            Type::get::<usize>(self.ctx),
        );
        let is_closure = self.builder.build_cmp(
            captures_rc_int,
            0usize.compile(self.ctx),
            Predicate::NotEqual,
        );
        is_closure.set_name("is_closure");
        let app_closure = |generator: &Self, _: &mut Env<'src, 'ctx>| {
            let captures_ptr = self.build_get_rc_contents_generic_ptr(captures_rc);
            let func = generator.builder.build_bit_cast(
                func_ptr,
                PointerType::new(FunctionType::new(
                    ret_type,
                    &[type_generic_ptr(self.ctx), arg_type],
                )),
            );
            let func = Function::from_super(func).expect("ICE: Failed to cast func to &Function");
            generator.builder.build_call(func, &[captures_ptr, arg])
        };
        let app_func = |generator: &Self, _: &mut Env<'src, 'ctx>| {
            let func = generator.builder.build_bit_cast(
                func_ptr,
                PointerType::new(FunctionType::new(ret_type, &[arg_type])),
            );
            let func = Function::from_super(func).expect("ICE: Failed to cast func to &Function");
            generator.builder.build_call(func, &[arg])
        };
        self.build_if(env, is_closure, app_closure, app_func)
    }

    // TODO: Tail call optimization
    /// Generates IR code for a function application.
    fn gen_app(&self, env: &mut Env<'src, 'ctx>, app: &'ast ast::App<'src>) -> &'ctx Value {
        let (at, rt) = app.func.get_type().get_func().unwrap();
        let (arg_type, ret_type) = (self.gen_type(at), self.gen_type(rt));
        let arg = self.gen_expr(env, &app.arg, None);
        // The expression being called will compile to a union of either a plain function or a
        // closure with a refcounted struct of captures. If the captures pointer is null, it's a
        // plain function. Otherwise, treat it as a closure
        let func = self.gen_expr(env, &app.func, None);
        self.build_app(env, func, (arg, arg_type), ret_type)
    }

    /// Generate the anonymous function of a closure
    ///
    /// A closure is represented as a structure of the environment it captures, and
    /// a function to pass this environment to, together with the argument, when the closure
    /// is applied to an argument.
    fn gen_closure_anon_func(
        &self,
        env: &mut Env<'src, 'ctx>,
        free_vars: &FreeVarInsts<'src>,
        lam: &'ast ast::Lambda<'src>,
        name: Option<&str>,
    ) -> &'ctx Function {
        let lambda_name = match name {
            Some(name) => format!("__lambda_{}", name),
            None => format!("lambda"),
        };
        let func = self.gen_func_decl(&lambda_name, &lam.typ);
        let parent_func = mem::replace(&mut *self.current_func.borrow_mut(), Some(func));
        let entry = func.append("entry");
        self.builder.position_at_end(entry);

        let captures_ptr_type = PointerType::new(self.captures_type_of_free_vars(free_vars));
        let captures_ptr_generic = &*func[0];
        captures_ptr_generic.set_name("captures_generic");
        let captures_ptr = self.builder.build_bit_cast(
            captures_ptr_generic,
            captures_ptr_type,
        );
        captures_ptr.set_name("captures");
        let param = &*func[1];
        param.set_name(lam.param_ident.s);

        // Create function local environment of only parameter + captures
        let mut local_env = map_of(lam.param_ident.s, vec![map_of(vec![], param)]);

        // Extract individual free variable captures from captures pointer and add to local env
        let mut i: usize = 0;
        for (fv_id, fv_insts) in free_vars.iter() {
            local_env.entry(fv_id).or_insert(vec![BTreeMap::new()]);
            for (fv_inst, _) in fv_insts.iter().cloned() {
                let fv_ptr = self.builder.build_gep(
                    captures_ptr,
                    &[0usize.compile(self.ctx), i.compile(self.ctx)],
                );
                fv_ptr.set_name(&format!("capt_{}", fv_id));
                let fv_loaded = self.builder.build_load(fv_ptr);
                fv_loaded.set_name(fv_id);
                local_env
                    .get_mut(fv_id)
                    .expect("ICE: fv_id not in local_env")
                    .last_mut()
                    .unwrap()
                    .insert(fv_inst, fv_loaded);
                i += 1;
            }
        }
        let old_vars = mem::replace(&mut env.vars, local_env);

        let e = self.gen_expr(env, &lam.body, None);
        self.builder.build_ret(e);

        // Restore state of code generator
        env.vars = old_vars;
        *self.current_func.borrow_mut() = parent_func;
        self.builder.position_at_end(
            self.current_block.borrow().expect(
                "ICE: no current_block",
            ),
        );

        func
    }

    /// Generate a call to the heap allocator to allocate `n` bytes of heap memory.
    ///
    /// Returns a heap pointer of generic type `i8*`, analogous to the way
    /// `malloc` in C returns a void pointer.
    ///
    /// Will call whatever function is bound to `malloc`.
    fn build_malloc(&self, env: &mut Env<'src, 'ctx>, n: u64) -> &'ctx Value {
        match env.get("malloc", &[]) {
            Some(Var::Func(f)) => self.builder.build_call(f, &[n.compile(self.ctx)]),
            Some(Var::Val(v)) => {
                self.build_app(
                    env,
                    v,
                    (n.compile(self.ctx), Type::get::<usize>(self.ctx)),
                    PointerType::new(Type::get::<u8>(self.ctx)),
                )
            }
            None => panic!("ICE: No allocator defined or declared"),
        }
    }

    /// Generate a call to the heap allocator to allocate heap space for a value of type `typ`
    ///
    /// Returns a heap pointer of type pointer to `typ`.
    fn build_malloc_of_type(&self, env: &mut Env<'src, 'ctx>, typ: &Type) -> &'ctx Value {
        let type_size = self.size_of(typ);
        let p = self.build_malloc(env, type_size);
        self.builder.build_bit_cast(p, PointerType::new(typ))
    }

    /// Put a value on the heap
    ///
    /// Returns a pointer pointing to `val` on the heap
    fn build_val_on_heap(&self, env: &mut Env<'src, 'ctx>, val: &Value) -> &'ctx Value {
        let p = self.build_malloc_of_type(env, val.get_type());
        self.builder.build_store(val, p);
        p
    }

    /// Build a sequence of instructions that create a struct in register
    /// and stores values in it
    pub fn build_struct(&self, vals: &[&'ctx Value]) -> &'ctx Value {
        let typ = StructType::new(
            self.ctx,
            &vals.iter().map(|v| v.get_type()).collect::<Vec<_>>(),
            false,
        );
        let mut out_struct = Value::new_undef(typ);
        for (i, val) in vals.iter().enumerate() {
            out_struct = self.builder.build_insert_value(out_struct, val, i);
        }
        out_struct
    }

    /// Build a reference counting pointer with contents `val`
    ///
    /// Count starts at 1
    fn build_rc(&self, env: &mut Env<'src, 'ctx>, val: &'ctx Value) -> &'ctx Value {
        let s = self.build_struct(&[1u64.compile(self.ctx), val]);
        self.build_val_on_heap(env, s)
    }

    /// Get a generic pointer to the contents of a rc pointer
    fn build_get_rc_contents_generic_ptr(&self, rc_generic: &Value) -> &'ctx Value {
        let rc = self.builder.build_bit_cast(
            rc_generic,
            PointerType::new(StructType::new(
                self.ctx,
                &[Type::get::<u64>(self.ctx), Type::get::<u8>(self.ctx)],
                false,
            )),
        );
        self.builder.build_gep(
            rc,
            &[
                0usize.compile(self.ctx),
                1u32.compile(self.ctx),
            ],
        )
    }

    /// Build instructions to cast a pointer value to a generic pointer `i8*`
    pub fn build_as_generic_ptr(&self, val: &Value) -> &'ctx Value {
        self.builder.build_bit_cast(val, type_generic_ptr(self.ctx))
    }

    /// Capture the free variables `free_vars` of some lambda from the environment `env`
    ///
    /// Returns a LLVM structure of each captured variable
    fn gen_lambda_env_capture(
        &self,
        env: &mut Env<'src, 'ctx>,
        free_vars: &FreeVarInsts<'src>,
    ) -> &'ctx Value {
        let mut captures_vals = Vec::new();
        for (&fv, insts) in free_vars {
            for &(ref inst, _) in insts {
                captures_vals.push(env.get_var(fv, inst).expect(
                    "ICE: Free var not found in env",
                ))
            }
        }
        self.build_struct(&captures_vals)
    }

    /// Generate the LLVM representation of a lambda expression, but with the contents
    /// of the closure capture left as allocated, but undefined, space
    ///
    /// For use when generating bindings with recursive references
    fn gen_lambda_no_capture(
        &self,
        env: &mut Env<'src, 'ctx>,
        lam: &'ast ast::Lambda<'src>,
        name: Option<&str>,
    ) -> (&'ctx Value, FreeVarInsts<'src>) {
        let free_vars = free_vars_in_lambda_filter_externs(&env, &lam);
        let func_ptr = self.gen_closure_anon_func(env, &free_vars, lam, name);
        let captures_type = self.captures_type_of_free_vars(&free_vars);
        let undef_heap_captures = self.build_malloc(env, self.size_of(captures_type));
        let undef_heap_captures_generic = self.build_as_generic_ptr(undef_heap_captures);
        let closure = self.build_struct(&[func_ptr, undef_heap_captures_generic]);
        (closure, free_vars)
    }

    /// For a closure that was created without environment capture,
    /// capture free variables and insert into captures member of struct
    ///
    /// May supply map of the free variables of the lambda, if saved from previously,
    /// to avoid unecessary recalculations.
    fn closure_capture_env(
        &self,
        env: &mut Env<'src, 'ctx>,
        closure: &Value,
        lam: &'ast ast::Lambda<'src>,
        free_vars: Option<FreeVarInsts<'src>>,
    ) {
        let free_vars = free_vars.unwrap_or_else(|| free_vars_in_lambda_filter_externs(&env, &lam));
        let captures = self.gen_lambda_env_capture(env, &free_vars);
        let closure_captures_rc_generic = self.builder.build_extract_value(closure, 1);
        let closure_captures_rc = self.builder.build_bit_cast(
            closure_captures_rc_generic,
            type_rc(self.ctx, captures.get_type()),
        );
        let closure_captures_ptr = self.builder.build_gep(
            closure_captures_rc,
            &[0usize.compile(self.ctx), 1u32.compile(self.ctx)],
        );
        self.builder.build_store(captures, closure_captures_ptr);
    }

    /// Generate the LLVM representation of a lambda expression
    fn gen_lambda(
        &self,
        env: &mut Env<'src, 'ctx>,
        lam: &'ast ast::Lambda<'src>,
        name: Option<&str>,
    ) -> &'ctx Value {
        let free_vars = free_vars_in_lambda_filter_externs(&env, &lam);
        let func_ptr = self.gen_closure_anon_func(env, &free_vars, lam, name);
        let captures = self.gen_lambda_env_capture(env, &free_vars);
        let captures_rc = self.build_rc(env, captures);
        let captures_rc_generic = self.build_as_generic_ptr(captures_rc);
        self.build_struct(&[func_ptr, captures_rc_generic])
    }

    /// Generate LLVM definitions for the variable/function bindings `bs`
    ///
    /// Assumes that the variable bindings in `bs` are in reverse topologically order
    /// for the relation: "depends on".
    fn gen_bindings(&self, env: &mut Env<'src, 'ctx>, bindings: &[&'ast ast::Binding<'src>]) {
        // To solve the problem of recursive references in closure captures, e.g. two mutually
        // recursive functions that need to capture each other: First create closures where
        // captures are left as allocated, but undefined space. Second, fill in captures
        // with all closures with pointers available to refer to.

        let empty_vec = vec![];
        // Flatten with regards to mono insts
        let mut bindings_insts: Vec<(_, &Vec<ast::Type>, _)> = Vec::new();
        for binding in bindings {
            env.push_var(binding.ident.s, BTreeMap::new());
            if binding.mono_insts.is_empty() {
                bindings_insts.push((binding.ident.s, &empty_vec, &binding.val));
            } else {
                for (inst_ts, val_inst) in &binding.mono_insts {
                    bindings_insts.push((binding.ident.s, &inst_ts, val_inst));
                }
            }
        }

        let mut lambdas_free_vars = VecDeque::new();
        for &(name, inst, val) in &bindings_insts {
            match *val {
                ast::Expr::Lambda(ref lam) => {
                    let (closure, free_vars) = self.gen_lambda_no_capture(env, lam, Some(name));
                    env.add_inst(name, inst.clone(), closure);
                    lambdas_free_vars.push_back(free_vars);
                }
                _ => (),
            }
        }

        for &(name, inst, val) in &bindings_insts {
            match val {
                &ast::Expr::Lambda(ref lam) => {
                    let closure = env.get_var(name, &inst).expect("ICE: variable dissapeared");
                    let free_vars = lambdas_free_vars.pop_front();
                    self.closure_capture_env(env, closure, lam, free_vars);
                }
                expr => {
                    let var = self.gen_expr(env, expr, Some(name));
                    var.set_name(name);
                    env.add_inst(name, inst.clone(), var);
                }
            }
        }
    }

    fn gen_let(&self, env: &mut Env<'src, 'ctx>, l: &'ast ast::Let<'src>) -> &'ctx Value {
        let bindings = l.bindings.bindings().rev().collect::<Vec<_>>();
        self.gen_bindings(env, &bindings);
        let v = self.gen_expr(env, &l.body, None);
        for b in bindings {
            env.pop(b.ident.s);
        }
        v
    }


    fn gen_cons(&self, env: &mut Env<'src, 'ctx>, cons: &'ast ast::Cons<'src>) -> &'ctx Value {
        self.build_struct(
            &[
                self.gen_expr(env, &cons.car, Some("car")),
                self.gen_expr(env, &cons.cdr, Some("cdr")),
            ],
        )
    }

    /// Generate llvm code for an expression and return its llvm Value.
    fn gen_expr(
        &self,
        env: &mut Env<'src, 'ctx>,
        expr: &'ast Expr<'src>,
        name: Option<&str>,
    ) -> &'ctx Value {
        match *expr {
            // Represent Nil as the empty struct, unit
            Expr::Nil(_) => val_nil(self.ctx),
            Expr::NumLit(ref n) => self.gen_num(n),
            Expr::StrLit(ref s) => self.gen_str(s),
            Expr::Bool(ref b) => b.val.compile(self.ctx),
            Expr::Variable(ref var) => self.gen_variable(env, var),
            Expr::App(ref app) => self.gen_app(env, app),
            Expr::If(ref cond) => self.gen_if(env, cond),
            Expr::Lambda(ref lam) => self.gen_lambda(env, lam, name),
            Expr::Let(ref l) => self.gen_let(env, l),
            // All type ascriptions should be replaced at this stage
            Expr::TypeAscript(_) => unreachable!(),
            Expr::Cons(ref c) => self.gen_cons(env, c),
        }
    }

    /// Generate LLVM IR for the executable application defined in `module`.
    ///
    /// Declare external functions, define global variabled and functions, and define
    /// an entry-point that makes the program binary executable.
    ///
    /// To allow for run-time operations, e.g. heap allocation, in "constant" global definitions,
    /// wrap the definitions in the entry-point function. This moves initialization to run-time,
    /// whish in turn allows for these operations.
    ///
    /// Basically, transform this:
    /// ```
    /// (define foo ...)
    /// (define bar ...)
    /// (define (main) ...)
    /// ```
    /// to this:
    /// ```
    /// (define (main)
    ///   (let ((foo ...)
    ///         (bar ...)
    ///         (main' ...))
    ///     (main')))
    /// ```
    /// where `main'` is the user defined `main`, and `main` is a simple, C-abi compatible function.
    pub fn gen_executable(&mut self, module: &ast::Module) {
        let mut env = Env::new();

        // Generate extern declarations
        self.gen_extern_decls(&mut env, &module.externs);

        // Create wrapping, entry-point `main` function
        let main_type = ast::Type::new_func(ast::TYPE_NIL.clone(), ast::TYPE_NIL.clone());
        let main_wrapper = self.gen_extern_func_decl("main", &main_type);
        let entry = main_wrapper.append("entry");
        self.builder.position_at_end(entry);
        *self.current_func.borrow_mut() = Some(main_wrapper);
        *self.current_block.borrow_mut() = Some(entry);

        // Generate global definitions
        let global_bindings = module.globals.bindings().rev().collect::<Vec<_>>();
        self.gen_bindings(&mut env, &global_bindings);

        // Call user defined `main`
        let user_main = env.get_var("main", &[]).expect(
            "ICE: No user defined `main`",
        );
        let r = self.build_app(
            &mut env,
            user_main,
            (val_nil(self.ctx), type_nil(self.ctx)),
            type_nil(self.ctx),
        );
        self.builder.build_ret(r);
    }
}
