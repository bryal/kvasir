use lib::front::{SrcPos, error_exit, exit};
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
    for (k, v) in es.iter().flat_map(|e2| free_vars_in_expr(e2)) {
        fvs.entry(k).or_insert(BTreeSet::new()).extend(v)
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
                    // Apply instantiation to type to remove wrapping `App`
                    v.typ.canonicalize(),
                )),
            )
        }
        App(box ref a) => free_vars_in_exprs(&[&a.func, &a.arg]),
        If(ref i) => free_vars_in_exprs(&[&i.predicate, &i.consequent, &i.alternative]),
        Lambda(box ref l) => free_vars_in_lambda(l),
        Let(box ref l) => {
            let mut es = vec![&l.body];
            for binding in l.bindings.bindings() {
                if binding.typ.is_monomorphic() {
                    es.push(&binding.val)
                } else {
                    es.extend(binding.mono_insts.values())
                }
            }
            let mut fvs = free_vars_in_exprs(&es);
            for b in l.bindings.bindings() {
                fvs.remove(b.ident.s);
            }
            fvs
        }
        TypeAscript(_) => panic!("free_vars_in_expr encountered TypeAscript"),
        Cons(box ref c) => free_vars_in_exprs(&[&c.car, &c.cdr]),
        Car(box ref c) => free_vars_in_expr(&c.expr),
        Cdr(box ref c) => free_vars_in_expr(&c.expr),
        Cast(ref c) => free_vars_in_expr(&c.expr),
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
        .filter(|&(k, _)| !env.externs.contains_key(k))
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

/// Naked function version of extern is used for external linkage and to call if direct call
/// to extern. If function is used as a value, e.g. put in a list together with arbitrary
/// functions, we have to wrap it in a closure so that it can be called in the same way as
/// any other function.
#[derive(Debug, Clone, Copy)]
struct Extern<'ctx> {
    func: &'ctx Function,
    closure: &'ctx Function,
}

/// A variable in the environment. Either an extern, or not
enum Var<'ctx> {
    Extern(Extern<'ctx>),
    Val(&'ctx Value),
}

#[derive(Debug)]
struct Env<'src, 'ctx> {
    externs: BTreeMap<String, Extern<'ctx>>,
    vars: BTreeMap<&'src str, Vec<BTreeMap<Vec<ast::Type<'src>>, &'ctx Value>>>,
}

impl<'src, 'ctx> Env<'src, 'ctx> {
    fn new() -> Self {
        Env {
            externs: BTreeMap::new(),
            vars: BTreeMap::new(),
        }
    }

    fn get_var_insts(&self, s: &str) -> Option<&BTreeMap<Vec<ast::Type<'src>>, &'ctx Value>> {
        self.vars.get(s).and_then(|l| l.last())
    }

    fn get_var(&self, s: &str, ts: &[ast::Type]) -> Option<&'ctx Value> {
        self.get_var_insts(s).and_then(|is| is.get(ts)).map(|&x| x)
    }

    fn get(&self, s: &str, ts: &[ast::Type]) -> Option<Var<'ctx>> {
        let val = self.get_var(s, ts).map(Var::Val);
        let ext = self.externs.get(s).map(|&x| Var::Extern(x));
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

struct NamedTypes<'ctx> {
    nil: &'ctx Type,
    real_world: &'ctx Type,
}

/// A codegenerator that visits all nodes in the AST, wherein it builds expressions
pub struct CodeGenerator<'ctx> {
    ctx: &'ctx Context,
    pub module: &'ctx Module,
    builder: &'ctx Builder,
    /// The function currently being built
    current_func: RefCell<Option<&'ctx Function>>,
    current_block: RefCell<Option<&'ctx BasicBlock>>,
    named_types: NamedTypes<'ctx>,
}
impl<'src: 'ast, 'ast, 'ctx> CodeGenerator<'ctx> {
    pub fn new(ctx: &'ctx Context, builder: &'ctx Builder, module: &'ctx Module) -> Self {
        let named_types = NamedTypes {
            real_world: StructType::new_named(ctx, "RealWorld", &[], false),
            nil: StructType::new_named(ctx, "Nil", &[], false),
        };
        CodeGenerator {
            ctx: ctx,
            module: module,
            builder: builder,
            current_func: RefCell::new(None),
            current_block: RefCell::new(None),
            named_types: named_types,
        }
    }

    fn new_nil_val(&self) -> &'ctx Value {
        Value::new_undef(self.named_types.nil)
    }

    fn target_data(&self) -> &'ctx TargetData {
        unsafe {
            let module_ref = mem::transmute::<&Module, LLVMModuleRef>(self.module);
            let target_data = mem::transmute::<LLVMTargetDataRef, &TargetData>(
                llvm_sys::target::LLVMGetModuleDataLayout(module_ref),
            );
            target_data
        }
    }

    fn size_of(&self, t: &Type) -> u64 {
        self.target_data().size_of(t)
    }

    fn ptr_size_bits(&self) -> usize {
        self.target_data().get_pointer_size()
    }

    fn gen_int_ptr_type(&self) -> &'ctx Type {
        match self.ptr_size_bits() * 8 {
            8 => Type::get::<i8>(self.ctx),
            16 => Type::get::<i16>(self.ctx),
            32 => Type::get::<i32>(self.ctx),
            64 => Type::get::<i64>(self.ctx),
            e => panic!("ICE: Platform has unsupported pointer size of {} bit", e),
        }
    }

    fn gen_func_type(&self, arg: &ast::Type<'src>, ret: &ast::Type<'src>) -> &'ctx Type {
        FunctionType::new(
            self.gen_type(ret),
            &[type_generic_ptr(self.ctx), self.gen_type(arg)],
        )
    }

    fn gen_type(&self, typ: &'ast ast::Type<'src>) -> &'ctx Type {
        match *typ {
            ast::Type::Var(ref tv) if tv.constrs.len() == 1 && tv.constrs.contains("Num") => {
                Type::get::<isize>(self.ctx)
            }
            ast::Type::Var { .. } => panic!("Type was Unknown at compile time"),
            ast::Type::Const("Int8", _) => Type::get::<i8>(self.ctx),
            ast::Type::Const("Int16", _) => Type::get::<i16>(self.ctx),
            ast::Type::Const("Int32", _) => Type::get::<i32>(self.ctx),
            ast::Type::Const("Int64", _) => Type::get::<i64>(self.ctx),
            ast::Type::Const("IntPtr", _) |
            ast::Type::Const("UIntPtr", _) => self.gen_int_ptr_type(),
            ast::Type::Const("UInt8", _) => Type::get::<u8>(self.ctx),
            ast::Type::Const("UInt16", _) => Type::get::<u16>(self.ctx),
            ast::Type::Const("UInt32", _) => Type::get::<u32>(self.ctx),
            ast::Type::Const("UInt64", _) => Type::get::<u64>(self.ctx),
            ast::Type::Const("Bool", _) => Type::get::<bool>(self.ctx),
            ast::Type::Const("Float32", _) => Type::get::<f32>(self.ctx),
            ast::Type::Const("Float64", _) => Type::get::<f64>(self.ctx),
            ast::Type::Const("Nil", _) => self.named_types.nil,
            ast::Type::Const("RealWorld", _) => self.named_types.real_world,
            ast::Type::App(box ast::TypeFunc::Const(s), ref ts) => {
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

    fn gen_func_decl(&self, id: String, typ: &ast::Type<'src>) -> &'ctx mut Function {
        let (arg, ret) = typ.get_func().expect(&format!(
            "ICE: Invalid function type `{}`",
            typ
        ));
        let func_typ = self.gen_func_type(arg, ret);
        self.module.add_function(&id, func_typ)
    }

    /// Generate an external function declaration and matching closure-wrapping
    fn gen_extern_func_decl(&self, id: String, typ: &ast::Type<'src>) -> &'ctx mut Function {
        assert!(
            self.current_block.borrow().is_none(),
            "ICE: External function declarations may only be generated first"
        );
        let (at, rt) = typ.get_func().expect(&format!(
            "ICE: Invalid function type `{}`",
            typ
        ));
        let (arg_type, ret_type) = (self.gen_type(at), self.gen_type(rt));
        let func_type = FunctionType::new(ret_type, &[arg_type]);
        self.module.add_function(&id, func_type)
    }

    /// Generate a dummy closure value that wraps a call to a plain function
    fn gen_wrapping_closure(
        &self,
        func: &'ctx Function,
        id: String,
        func_type: &ast::Type,
    ) -> &'ctx Function {
        let (at, rt) = func_type.get_func().expect(&format!(
            "ICE: Invalid function type `{}`",
            func_type
        ));
        let (arg_type, ret_type) = (self.gen_type(at), self.gen_type(rt));
        let clos_typ = FunctionType::new(ret_type, &[type_generic_ptr(self.ctx), arg_type]);
        let closure = self.module.add_function(
            &format!("{}_closure", id),
            &clos_typ,
        );
        let entry = closure.append("entry");
        self.builder.position_at_end(entry);
        closure[0].set_name("_NO_CAPTURES");
        let param = &*closure[1];
        let r = self.builder.build_call(func, &[param]);
        self.builder.build_ret(r);
        closure
    }

    /// Generate an external function declaration and matching closure-wrapping
    fn gen_extern_func(&self, id: String, typ: &ast::Type<'src>) -> Extern<'ctx> {
        assert!(
            self.current_block.borrow().is_none(),
            "ICE: External function declarations may only be generated first"
        );
        let func = self.gen_extern_func_decl(id.clone(), typ);
        let closure = self.gen_wrapping_closure(func, id, typ);
        Extern { func, closure }
    }

    /// Generates a simple binop function of the instruction built by `build_instr`
    fn gen_binop_func(
        &self,
        func_name: String,
        typ: &ast::Type<'src>,
        build_instr: fn(&'ctx Builder, &'ctx Value, &'ctx Value) -> &'ctx Value,
    ) -> Extern<'ctx> {
        let func = self.gen_extern_func_decl(func_name.clone(), typ);
        let entry = func.append("entry");
        self.builder.position_at_end(entry);
        let a = self.builder.build_extract_value(&*func[0], 0);
        let b = self.builder.build_extract_value(&*func[0], 1);
        let r = build_instr(self.builder, a, b);
        self.builder.build_ret(r);

        let closure = self.gen_wrapping_closure(func, func_name, typ);
        Extern { func, closure }
    }

    fn gen_core_funcs(&self, env: &mut Env<'src, 'ctx>) {
        type BinopBuilder<'ctx> = fn(&'ctx Builder, &'ctx Value, &'ctx Value) -> &'ctx Value;
        assert!(
            self.current_block.borrow().is_none(),
            "ICE: Core functions may only be generated before main"
        );

        // Generate arithmeric, relational, and logic binops, e.g. addition
        let int_types = ["Int8", "Int16", "Int32", "Int64"];
        let uint_types = ["UInt8", "UInt16", "UInt32", "UInt64"];
        let float_types = ["Float32", "Float64"];
        let arithm_binops = [
            ("add", Builder::build_add as BinopBuilder<'ctx>),
            ("sub", Builder::build_sub),
            ("mul", Builder::build_mul),
        ];
        let int_arithm_binops = [
            ("div", Builder::build_sdiv as BinopBuilder<'ctx>),
            ("shl", Builder::build_shl),
            ("shr", Builder::build_shl),
        ];
        let uint_arithm_binops = [
            ("div", Builder::build_udiv as BinopBuilder<'ctx>),
            ("shl", Builder::build_shl),
            ("shr", Builder::build_shl),
        ];
        let float_arithm_binops = [("div", Builder::build_fdiv as BinopBuilder<'ctx>)];
        let relational_binops = [
            ("eq", Builder::build_eq as BinopBuilder<'ctx>),
            ("neq", Builder::build_neq),
            ("gt", Builder::build_gt),
            ("gteq", Builder::build_gteq),
            ("lt", Builder::build_lt),
            ("lteq", Builder::build_lteq),
        ];
        let logic_binops = [
            ("and", Builder::build_and as BinopBuilder<'ctx>),
            ("or", Builder::build_or),
            ("xor", Builder::build_xor),
        ];
        let num_classes_with_extras = [
            (&int_types[..], &int_arithm_binops[..]),
            (&uint_types[..], &uint_arithm_binops[..]),
            (&float_types[..], &float_arithm_binops[..]),
        ];
        for &(num_class, extras) in &num_classes_with_extras {
            for type_name in num_class {
                let arithms_with_div = arithm_binops
                    .iter()
                    .chain(extras)
                    .cloned()
                    .collect::<Vec<_>>();
                let typ = ast::Type::Const(type_name, None);
                let binop_type = ast::Type::new_binop(typ.clone());
                let relational_binop_type = ast::Type::new_relational_binop(typ);
                let logic_binop_type = ast::Type::new_logic_binop();
                let ops_with_type = [
                    (&arithms_with_div[..], binop_type),
                    (&relational_binops[..], relational_binop_type),
                    (&logic_binops[..], logic_binop_type),
                ];
                for &(ops, ref op_type) in &ops_with_type {
                    for &(op_name, build_op) in ops {
                        let func_name = format!("{}-{}", op_name, type_name);
                        env.externs.insert(
                            func_name.clone(),
                            self.gen_binop_func(func_name, op_type, build_op),
                        );
                    }
                }
            }
        }
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
                id.to_string(),
                self.gen_extern_func(id.to_string(), &decl.typ),
            );
        }
        // Heap allocation is required for core-functionality. Unless user has already
        // explicitly declared the allocator, add it.
        if !externs.contains_key("malloc") {
            let malloc_type = ast::Type::new_func(
                ast::Type::Const("UIntPtr", None),
                ast::Type::new_ptr(ast::Type::Const("UInt8", None)),
            );
            env.externs.insert(
                "malloc".to_string(),
                self.gen_extern_func("malloc".to_string(), &malloc_type),
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
            // If it's an arbitrary number, default to isize (Int)
            ast::Type::Var(ref tv) if tv.constrs.len() == 1 && tv.constrs.contains("Num") => {
                CodeGenerator::parse_gen_lit::<isize>
            }
            ast::Type::Const("Int8", _) => CodeGenerator::parse_gen_lit::<i8>,
            ast::Type::Const("Int16", _) => CodeGenerator::parse_gen_lit::<i16>,
            ast::Type::Const("Int32", _) => CodeGenerator::parse_gen_lit::<i32>,
            ast::Type::Const("Int64", _) => CodeGenerator::parse_gen_lit::<i64>,
            ast::Type::Const("IntPtr", _) => CodeGenerator::parse_gen_lit::<isize>,
            ast::Type::Const("UInt8", _) => CodeGenerator::parse_gen_lit::<u8>,
            ast::Type::Const("UInt16", _) => CodeGenerator::parse_gen_lit::<u16>,
            ast::Type::Const("UInt32", _) => CodeGenerator::parse_gen_lit::<u32>,
            ast::Type::Const("UInt64", _) => CodeGenerator::parse_gen_lit::<u64>,
            ast::Type::Const("UIntPtr", _) => CodeGenerator::parse_gen_lit::<usize>,
            ast::Type::Const("Bool", _) => CodeGenerator::parse_gen_lit::<bool>,
            ast::Type::Const("Float32", _) => CodeGenerator::parse_gen_lit::<f32>,
            ast::Type::Const("Float64", _) => CodeGenerator::parse_gen_lit::<f64>,
            _ => {
                num.pos.error_exit(
                    ICE("type of numeric literal is not numeric".into()),
                )
            }
        };
        parser(self, &num.lit, &num.typ, &num.pos)
    }

    fn gen_str(&self, lit: &'ast ast::StrLit<'src>) -> &'ctx Value {
        let str_lit_ll = Value::new_string(self.ctx, &lit.lit, true);
        let str_const = self.module.add_global_variable("str_lit", str_lit_ll);
        str_const.set_constant(true);
        let str_ptr = self.builder.build_gep(
            str_const,
            &[0usize.compile(self.ctx), 0usize.compile(self.ctx)],
        );
        self.build_struct(&[lit.lit.len().compile(self.ctx), str_ptr])
    }

    /// Generate IR for a variable used as an r-value
    fn gen_variable(&self, env: &mut Env<'src, 'ctx>, var: &'ast ast::Variable) -> &'ctx Value {
        let arithm_binops = hashset!{ "add", "sub", "mul", "div" };
        let relational_binops = hashset!{ "eq", "neq", "gt", "gteq", "lt", "lteq" };
        let logic_binops = hashset!{ "and", "or", "xor" };

        let inst = var.typ.get_inst_args().unwrap_or(&[]);
        let type_canon = var.typ.canonicalize();
        match env.get(var.ident.s, inst) {
            // NOTE: Ugly hack to fix generic codegen for some binops
            _ if arithm_binops.contains(var.ident.s) => {
                let maybe_op_typ = type_canon.get_cons_binop().map(|t| t.num_to_int64());
                let op_typ = maybe_op_typ.unwrap_or_else(|| {
                    panic!("ICE: binop has bad type {}", type_canon)
                });
                assert!(
                    op_typ.is_int() || op_typ.is_uint() || op_typ.is_float(),
                    "ICE: binop has bad type {}",
                    type_canon
                );
                let typ = ast::Type::new_binop(op_typ.clone());
                let f = format!("{}-{}", var.ident.s, op_typ.get_const().unwrap());
                let mut var2 = var.clone();
                var2.typ = typ;
                var2.ident.s = &f;
                self.gen_variable(env, &var2)
            }
            _ if relational_binops.contains(var.ident.s) => {
                let maybe_op_typ = type_canon.get_cons_relational_binop().map(
                    |t| t.num_to_int64(),
                );
                let op_typ = maybe_op_typ.unwrap_or_else(|| {
                    panic!("ICE: binary relational op has bad type {}", type_canon)
                });
                assert!(
                    op_typ.is_int() || op_typ.is_uint() || op_typ.is_float(),
                    "ICE: relational binop has bad type {}",
                    type_canon
                );
                let typ = ast::Type::new_relational_binop(op_typ.clone());
                let f = format!("{}-{}", var.ident.s, op_typ.get_const().unwrap());
                let mut var2 = var.clone();
                var2.typ = typ;
                var2.ident.s = &f;
                self.gen_variable(env, &var2)
            }
            _ if logic_binops.contains(var.ident.s) => {
                assert!(
                    type_canon.is_cons_logic_binop(),
                    "ICE: relational binop has bad type {}",
                    type_canon
                );
                let typ = ast::Type::new_logic_binop();
                let f = format!("{}", var.ident.s);
                let mut var2 = var.clone();
                var2.typ = typ;
                var2.ident.s = &f;
                self.gen_variable(env, &var2)
            }
            Some(Var::Extern(e)) => {
                Value::new_struct(
                    self.ctx,
                    &[e.closure, Value::new_undef(type_rc_generic(self.ctx))],
                    false,
                )
            }
            Some(Var::Val(v)) => v,
            // Undefined variables are caught during type check/inference
            None => {
                panic!(
                    "ICE: Undefined variable at codegen: {} inst `{:?}`\ninsts of {}: {:#?}",
                    var.ident.s,
                    inst,
                    var.ident.s,
                    env.get_var_insts(var.ident.s)
                )
            }
        }
    }

    fn gen_if(&self, env: &mut Env<'src, 'ctx>, cond: &'ast ast::If<'src>) -> &'ctx Value {
        let parent_func = self.current_func.borrow().unwrap();
        let then_br = parent_func.append("cond_then");
        let else_br = parent_func.append("cond_else");
        let next_br = parent_func.append("cond_next");
        let pred = self.gen_expr(env, &cond.predicate, None);
        self.builder.build_cond_br(pred, then_br, else_br);
        let mut phi_nodes = vec![];

        self.builder.position_at_end(then_br);
        *self.current_block.borrow_mut() = Some(then_br);
        let then_val = self.gen_expr(env, &cond.consequent, None);
        let then_last_block = self.current_block.borrow().unwrap();
        phi_nodes.push((then_val, then_last_block));
        self.builder.build_br(next_br);

        self.builder.position_at_end(else_br);
        *self.current_block.borrow_mut() = Some(else_br);
        let else_val = self.gen_expr(env, &cond.alternative, None);
        let else_last_block = self.current_block.borrow().unwrap();
        phi_nodes.push((else_val, else_last_block));
        self.builder.build_br(next_br);

        self.builder.position_at_end(next_br);
        *self.current_block.borrow_mut() = Some(next_br);
        self.builder.build_phi(then_val.get_type(), &phi_nodes)
    }

    /// Build the application of a function to an argument
    fn build_app(
        &self,
        closure: &'ctx Value,
        (arg, arg_type): (&'ctx Value, &'ctx Type),
        ret_type: &'ctx Type,
    ) -> &'ctx Value {
        let func_ptr = self.builder.build_extract_value(closure, 0);
        let captures_rc = self.builder.build_extract_value(closure, 1);
        let captures_ptr = self.build_get_rc_contents_generic_ptr(captures_rc);
        let func = self.builder.build_bit_cast(
            func_ptr,
            PointerType::new(FunctionType::new(
                ret_type,
                &[type_generic_ptr(self.ctx), arg_type],
            )),
        );
        let func = Function::from_super(func).expect("ICE: Failed to cast func to &Function");
        self.builder.build_call(func, &[captures_ptr, arg])
    }

    // TODO: Tail call optimization
    /// Generates IR code for a function application.
    fn gen_app(&self, env: &mut Env<'src, 'ctx>, app: &'ast ast::App<'src>) -> &'ctx Value {
        let typ = app.func.get_type();
        let inst = typ.get_inst_args().unwrap_or(&[]);
        let canon = typ.canonicalize();
        let (at, rt) = canon.get_func().expect(&format!(
                "ICE: Invalid function type `{}`",
                app.func.get_type(),
            ));
        let (arg_type, ret_type) = (self.gen_type(at), self.gen_type(rt));
        let arg = self.gen_expr(env, &app.arg, None);

        // If it's a direct application of an extern, call it as a function,
        // otherwise call it as a closure
        if let Some(Var::Extern(ext)) = app.func.as_var().and_then(|v| env.get(v.ident.s, inst)) {
            self.builder.build_call(ext.func, &[arg])
        } else {
            let func = self.gen_expr(env, &app.func, None);
            self.build_app(func, (arg, arg_type), ret_type)
        }
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
        let func = self.gen_func_decl(lambda_name, &lam.typ);
        let parent_func = mem::replace(&mut *self.current_func.borrow_mut(), Some(func));
        let entry = func.append("entry");
        let parent_block = mem::replace(&mut *self.current_block.borrow_mut(), Some(entry));
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
        let mut i: u32 = 0;
        for (fv_id, fv_insts) in free_vars.iter() {
            local_env.entry(fv_id).or_insert(vec![BTreeMap::new()]);
            for (fv_inst, _) in fv_insts.iter().cloned() {
                let fv_ptr = self.builder.build_gep(
                    captures_ptr,
                    &[0usize.compile(self.ctx), i.compile(self.ctx)],
                );
                fv_ptr.set_name(&format!("capture_{}", fv_id));
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
        *self.current_block.borrow_mut() = parent_block;
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
            Some(Var::Extern(ext)) => self.builder.build_call(ext.func, &[n.compile(self.ctx)]),
            Some(Var::Val(v)) => {
                self.build_app(
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

    /// Build instructions to cast a pointer value to a generic
    /// reference counted pointer `{i64, i8}*`
    pub fn build_as_generic_rc(&self, val: &Value) -> &'ctx Value {
        self.builder.build_bit_cast(val, type_rc_generic(self.ctx))
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
                captures_vals.push(env.get_var(fv, inst).expect(&format!(
                    "ICE: Free var not found in env\n\
                     var: {}, inst: {:?}\n\
                     env: {:?}",
                    fv,
                    inst,
                    env
                )))
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
        let undef_heap_captures_generic_rc = self.build_as_generic_rc(undef_heap_captures);
        let closure = self.build_struct(&[func_ptr, undef_heap_captures_generic_rc]);
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
        let captures_rc_generic = self.builder.build_bit_cast(
            captures_rc,
            type_rc_generic(self.ctx),
        );
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
            if binding.typ.is_monomorphic() {
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

    /// Generate LLVM IR for a `let` special form
    fn gen_let(&self, env: &mut Env<'src, 'ctx>, l: &'ast ast::Let<'src>) -> &'ctx Value {
        let bindings = l.bindings.bindings().rev().collect::<Vec<_>>();
        self.gen_bindings(env, &bindings);
        let v = self.gen_expr(env, &l.body, None);
        for b in bindings {
            env.pop(b.ident.s);
        }
        v
    }

    /// Generate LLVM IR for the construction of a `cons` pair
    fn gen_cons(&self, env: &mut Env<'src, 'ctx>, cons: &'ast ast::Cons<'src>) -> &'ctx Value {
        self.build_struct(
            &[
                self.gen_expr(env, &cons.car, Some("car")),
                self.gen_expr(env, &cons.cdr, Some("cdr")),
            ],
        )
    }

    /// Generate LLVM IR for the extraction of the first element of a `cons` pair
    fn gen_car(&self, env: &mut Env<'src, 'ctx>, c: &'ast ast::Car<'src>) -> &'ctx Value {
        let cons = self.gen_expr(env, &c.expr, Some("cons"));
        self.builder.build_extract_value(cons, 0)
    }

    /// Generate LLVM IR for the extraction of the second element of a `cons` pair
    fn gen_cdr(&self, env: &mut Env<'src, 'ctx>, c: &'ast ast::Cdr<'src>) -> &'ctx Value {
        let cons = self.gen_expr(env, &c.expr, Some("cons"));
        self.builder.build_extract_value(cons, 1)
    }

    /// Generate LLVM IR for the cast of an expression to a type
    fn gen_cast(&self, env: &mut Env<'src, 'ctx>, c: &'ast ast::Cast<'src>) -> &'ctx Value {
        let ptr_size = self.ptr_size_bits();
        let from_type = c.expr.get_type();
        let to_type = &c.typ;
        let to_type_ll = self.gen_type(to_type);
        let from_expr = self.gen_expr(env, &c.expr, None);
        let res = if let Some(from_size) = from_type.int_size(ptr_size) {
            // Casting from signed integer
            if let Some(to_size) = to_type.int_size(ptr_size).or(to_type.uint_size(ptr_size)) {
                // to some integer type
                if from_size < to_size {
                    Some(self.builder.build_sext(from_expr, to_type_ll))
                } else if from_size > to_size {
                    Some(self.builder.build_trunc(from_expr, to_type_ll))
                } else {
                    Some(from_expr)
                }
            } else if to_type.is_float() {
                // to some float type
                Some(self.builder.build_si_to_fp(from_expr, to_type_ll))
            } else {
                None
            }
        } else if let Some(from_size) = from_type.uint_size(ptr_size) {
            // Casting from unsigned integer
            if let Some(to_size) = to_type.int_size(ptr_size).or(to_type.uint_size(ptr_size)) {
                // to some integer type
                if from_size < to_size {
                    Some(self.builder.build_zext(from_expr, to_type_ll))
                } else if from_size > to_size {
                    Some(self.builder.build_trunc(from_expr, to_type_ll))
                } else {
                    Some(from_expr)
                }
            } else if to_type.is_float() {
                // to some float type
                Some(self.builder.build_ui_to_fp(from_expr, to_type_ll))
            } else {
                None
            }
        } else if from_type.is_float() {
            // Casting from float
            if to_type.is_float() {
                // to some float type
                Some(self.builder.build_fpcast(from_expr, to_type_ll))
            } else if to_type.is_int() {
                // to some signed integer type
                Some(self.builder.build_fp_to_si(from_expr, to_type_ll))
            } else if to_type.is_uint() {
                // to some unsigned integer type
                Some(self.builder.build_fp_to_ui(from_expr, to_type_ll))
            } else {
                None
            }
        } else {
            None
        };
        res.unwrap_or_else(|| {
            c.pos.error_exit(format!(
                "Invalid cast\nCannot cast from {} to {}",
                from_type,
                to_type
            ))
        })
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
            Expr::Nil(_) => self.new_nil_val(),
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
            Expr::Car(ref c) => self.gen_car(env, c),
            Expr::Cdr(ref c) => self.gen_cdr(env, c),
            Expr::Cast(ref c) => self.gen_cast(env, c),
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
        // Assert that `main` exists and is monomorphic of type `(-> Nil Nil)`
        {
            let main = module
                .globals
                .bindings()
                .find(|b| b.ident.s == "main")
                .unwrap_or_else(|| error_exit("main function not found"));
            let expect = ast::Type::new_io(ast::TYPE_NIL.clone());
            if main.typ != expect {
                let error_msg = format!(
                    "main function has wrong type. Expected type `{}`, found type `{}`",
                    expect,
                    main.typ
                );
                if main.typ.is_monomorphic() {
                    main.pos.error_exit(error_msg)
                } else {
                    main.pos.error(error_msg);
                    main.pos.help(
                        "Try adding type annotations to enforce correct type \
                         during type-checking.\n\
                         E.g. `(define main (: (lambda (_) ...) (-> Nil Nil)))`",
                    );
                    exit()
                }
            }
        }

        let mut env = Env::new();

        // Generate core functions
        self.gen_core_funcs(&mut env);

        // Generate extern declarations
        self.gen_extern_decls(&mut env, &module.externs);

        // Create wrapping, entry-point `main` function
        let main_type = FunctionType::new(self.named_types.nil, &[self.named_types.nil]);
        let main_wrapper = self.module.add_function("main", &main_type);
        let entry = main_wrapper.append("entry");
        self.builder.position_at_end(entry);
        *self.current_func.borrow_mut() = Some(main_wrapper);
        *self.current_block.borrow_mut() = Some(entry);

        // Generate global definitions
        let global_bindings = module.globals.bindings().rev().collect::<Vec<_>>();
        self.gen_bindings(&mut env, &global_bindings);

        // Call user defined `main`
        let user_main = env.get_var("main", &[]).expect(
            "ICE: No monomorphic user defined `main`",
        );
        let r = self.build_app(
            user_main,
            (self.new_nil_val(), self.named_types.nil),
            self.named_types.nil,
        );
        self.builder.build_ret(r);
    }
}
