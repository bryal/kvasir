use self::CodegenErr::*;
use lib::collections::ScopeStack;
use lib::front::SrcPos;
use lib::front::ast::{self, Expr};
use llvm::*;
use std::{fmt, mem};
use std::cell::RefCell;
use std::collections::HashMap;
use std::str::FromStr;

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

pub struct Env<'src: 'ast, 'ast, 'ctx> {
    funcs: ScopeStack<&'src str, &'ctx Function>,
    statics: ScopeStack<&'src str, (&'ctx GlobalVariable, &'ast Expr<'src>)>,
    vars: Vec<(&'src str, &'ctx Value)>,
}
impl<'src: 'ast, 'ast, 'ctx> Env<'src, 'ast, 'ctx> {
    pub fn new() -> Self {
        Env {
            funcs: ScopeStack::new(),
            statics: ScopeStack::new(),
            vars: Vec::new(),
        }
    }

    fn get_var(&self, id: &str) -> Option<&'ctx Value> {
        self.vars.iter().cloned().rev().find(|&(b, _)| b == id).map(|(_, t)| t)
    }
}

/// Add a static (global variable) to a module with the given type, name and value.
fn add_constant_static<'ctx>(module: &'ctx Module,
                             name: &str,
                             val: &'ctx Value)
                             -> &'ctx GlobalVariable {
    let glob = module.add_global_variable(name, val);
    glob.set_constant(true);
    glob
}

/// A codegenerator that visits all nodes in the AST, wherein it builds expressions
pub struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    pub module: &'ctx Module,
    target_data: CBox<TargetData>,
    builder: &'ctx Builder,
    /// The function currently being built
    building_func: RefCell<Option<&'ctx Function>>,
}
impl<'src: 'ast, 'ast, 'ctx> CodeGenerator<'ctx> {
    pub fn new(context: &'ctx Context, builder: &'ctx Builder, module: &'ctx Module) -> Self {
        CodeGenerator {
            context: context,
            module: module,
            target_data: TargetData::new(module.get_target()),
            builder: builder,
            building_func: RefCell::new(None),
        }
    }

    fn size_of(&self, typ: &Type) -> u64 {
        self.target_data.size_of(typ)
    }

    fn gen_nil(&self) -> &'ctx Value {
        Value::new_struct(self.context, &[], false)
    }

    fn gen_type(&self, typ: &'ast ast::Type<'src>) -> &'ctx Type {
        use lib::front::ast::Type as PType;

        match *typ {
            PType::Unknown => panic!("Type was Unknown at compile time"),
            PType::Basic("Int8") => Type::get::<i8>(self.context),
            PType::Basic("Int16") => Type::get::<i16>(self.context),
            PType::Basic("Int32") => Type::get::<i32>(self.context),
            PType::Basic("Int64") => Type::get::<i64>(self.context),
            PType::Basic("IntPtr") => Type::get::<isize>(self.context),
            PType::Basic("UInt8") => Type::get::<u8>(self.context),
            PType::Basic("UInt16") => Type::get::<u16>(self.context),
            PType::Basic("UInt32") => Type::get::<u32>(self.context),
            PType::Basic("UInt64") => Type::get::<u64>(self.context),
            PType::Basic("UIntPtr") => Type::get::<usize>(self.context),
            PType::Basic("Bool") => Type::get::<bool>(self.context),
            PType::Basic("Float32") => Type::get::<f32>(self.context),
            PType::Basic("Float64") => Type::get::<f64>(self.context),
            PType::Basic("Nil") => StructType::new(self.context, &[], false),
            PType::Construct("Proc", _) => {
                let (params, ret) = typ.get_proc_sig().unwrap();
                FunctionType::new(self.gen_type(ret),
                                  &params.iter()
                                         .map(|param| self.gen_type(param))
                                         .collect::<Vec<_>>())
            }
            PType::Construct("RawPtr", ref args) => PointerType::new(self.gen_type(&args[0])),
            _ => panic!("Type `{}` is not yet implemented", typ),
        }
    }

    fn parse_gen_lit<I>(&self, lit: &str, typ: &ast::Type<'src>, pos: &SrcPos<'src>) -> &'ctx Value
        where I: Compile<'ctx> + FromStr
    {
        lit.parse::<I>()
           .map(|n| n.compile(self.context))
           .unwrap_or_else(|_| pos.error_exit(CodegenErr::num_parse_err(typ)))
    }

    fn gen_num(&self, num: &ast::NumLit) -> &'ctx Value {
        let parser = match num.typ {
            ast::Type::Basic("Int8") => CodeGenerator::parse_gen_lit::<i8>,
            ast::Type::Basic("Int16") => CodeGenerator::parse_gen_lit::<i16>,
            ast::Type::Basic("Int32") => CodeGenerator::parse_gen_lit::<i32>,
            ast::Type::Basic("Int64") => CodeGenerator::parse_gen_lit::<i64>,
            ast::Type::Basic("IntPtr") => CodeGenerator::parse_gen_lit::<isize>,
            ast::Type::Basic("UInt8") => CodeGenerator::parse_gen_lit::<u8>,
            ast::Type::Basic("UInt16") => CodeGenerator::parse_gen_lit::<u16>,
            ast::Type::Basic("UInt32") => CodeGenerator::parse_gen_lit::<u32>,
            ast::Type::Basic("UInt64") => CodeGenerator::parse_gen_lit::<u64>,
            ast::Type::Basic("UIntPtr") => CodeGenerator::parse_gen_lit::<usize>,
            ast::Type::Basic("Bool") => CodeGenerator::parse_gen_lit::<bool>,
            ast::Type::Basic("Float32") => CodeGenerator::parse_gen_lit::<f32>,
            ast::Type::Basic("Float64") => CodeGenerator::parse_gen_lit::<f64>,
            _ => num.pos.error_exit(ICE("type of numeric literal is not numeric".into())),
        };
        parser(self, &num.lit, &num.typ, &num.pos)
    }

    /// Gets an array, `[N x TYPE]`, as a pointer to the first element, `TYPE*`
    fn get_array_as_ptr(&self, array_ptr: &'ctx Value) -> &'ctx Value {
        // First, deref ptr to array (index first element of ptr, like pointer indexing in C).
        // Second, get address of first element in array == address of array start
        self.builder.build_gep(array_ptr, &vec![0usize.compile(self.context); 2])
    }

    fn gen_str(&self, s: &'ast ast::StrLit<'src>) -> &'ctx Value {
        let bytes = s.lit.compile(self.context);

        let static_array = add_constant_static(&self.module, "str_lit", bytes);

        // A string literal is represented as a struct with a pointer to the byte array and the size
        // { i8* @lit.bytes, i64 /* machines ptr size */ 13 }
        //     where @lit.bytes = global [13 x i8] c"Hello, world!"
        Value::new_struct(self.context,
                          &[self.get_array_as_ptr(static_array), s.lit.len().compile(self.context)],
                          false)
    }

    fn gen_bool(&self, b: &'ast ast::Bool<'src>) -> &'ctx Value {
        if b.typ == ast::Type::Basic("Bool") {
            b.val.compile(self.context)
        } else {
            unimplemented!()
        }
    }

    /// Generate IR for a binding used as an r-value
    fn gen_r_binding(&self,
                     env: &mut Env<'src, 'ast, 'ctx>,
                     bnd: &'ast ast::Binding<'src>)
                     -> &'ctx Value {
        // Function pointers are returned as-is,
        // while statics and variables are loaded into registers
        env.statics
           .get(bnd.ident.s)
           .map(|&(ptr, _)| &***ptr)
           .or(env.get_var(bnd.ident.s))
           .map(|ptr| {
               let v = self.builder.build_load(ptr);
               v.set_name(&format!("{}_tmp", bnd.ident.s));
               v
           })
           .or(env.funcs
                  .get(bnd.ident.s)
                  .map(|&func| &***func))
           .unwrap_or_else(|| {
               bnd.ident.pos.error_exit(ICE("undefined binding at compile time".into()))
           })
    }

    /// Generates IR code for a procedure call. If the call is in a tail position and the call
    /// is a recursive call to the caller itself, make a tail call and return `Nothing`.
    /// Otherwise, make a normal call and return the result.
    fn gen_call(&self,
                env: &mut Env<'src, 'ast, 'ctx>,
                call: &'ast ast::Call<'src>)
                -> &'ctx Value {
        let proced = Function::from_super(self.gen_expr(env, &call.proced)).unwrap_or_else(|| {
            call.proced
                .pos()
                .error_exit(ICE("expression in procedure pos is not a function".into()))
        });

        let mut args = Vec::new();
        for arg in &call.args {
            args.push(self.gen_expr(env, arg))
        }

        self.builder.build_call(proced, &args)
    }

    fn gen_tail_call(&self, env: &mut Env<'src, 'ast, 'ctx>, call: &'ast ast::Call<'src>) {
        let proced = Function::from_super(self.gen_expr(env, &call.proced)).unwrap_or_else(|| {
            call.proced
                .pos()
                .error_exit(ICE("expression in procedure pos is not a function".into()))
        });

        let mut args = Vec::new();
        for arg in &call.args {
            args.push(self.gen_expr(env, arg))
        }

        let call = self.builder.build_call(proced, &args);

        self.builder.build_ret(call);
    }

    fn gen_handle_block<T, F>(&self,
                              env: &mut Env<'src, 'ast, 'ctx>,
                              block: &'ast ast::Block<'src>,
                              handler: F)
                              -> T
        where F: FnOnce(&Self, &mut Env<'src, 'ast, 'ctx>, &'ast Expr<'src>) -> T
    {
        self.gen_static_defs(env, &block.static_defs);

        let old_n_vars = env.vars.len();

        let (last, statements) = block.exprs.split_last().expect("no exprs in block");

        for statement in statements {
            self.gen_expr(env, statement);
        }

        let r = handler(self, env, last);

        env.vars.truncate(old_n_vars);
        env.funcs.pop();
        env.statics.pop();

        r
    }

    fn gen_block(&self,
                 env: &mut Env<'src, 'ast, 'ctx>,
                 block: &'ast ast::Block<'src>)
                 -> &'ctx Value {
        self.gen_handle_block(env, block, Self::gen_expr)
    }

    fn gen_tail_block(&self,
                      env: &mut Env<'src, 'ast, 'ctx>,
                      block: &'ast ast::Block<'src>)
                      -> Option<&'ctx Value> {
        self.gen_handle_block(env, block, Self::gen_tail_expr)
    }

    fn gen_if(&self,
              env: &mut Env<'src, 'ast, 'ctx>,
              cond: &'ast ast::If<'src>,
              typ: &ast::Type<'src>)
              -> &'ctx Value {
        let parent_func = self.building_func.borrow().unwrap();

        let then_br = parent_func.append("cond_then");
        let else_br = parent_func.append("cond_else");
        let next_br = parent_func.append("cond_next");

        self.builder.build_cond_br(self.gen_expr(env, &cond.predicate), then_br, else_br);

        let mut phi_nodes = vec![];

        self.builder.position_at_end(then_br);

        let then_val = self.gen_expr(env, &cond.consequent);
        phi_nodes.push((then_val, then_br));
        self.builder.build_br(next_br);


        self.builder.position_at_end(else_br);

        let else_val = self.gen_expr(env, &cond.alternative);
        phi_nodes.push((else_val, else_br));
        self.builder.build_br(next_br);

        self.builder.position_at_end(next_br);

        self.builder.build_phi(self.gen_type(typ), &phi_nodes)
    }

    fn gen_tail_if(&self,
                   env: &mut Env<'src, 'ast, 'ctx>,
                   cond: &'ast ast::If<'src>,
                   typ: &ast::Type<'src>)
                   -> Option<&'ctx Value> {
        let parent_func = self.building_func.borrow().unwrap();

        let then_br = parent_func.append("cond_then");
        let else_br = parent_func.append("cond_else");

        self.builder.build_cond_br(self.gen_expr(env, &cond.predicate), then_br, else_br);

        let mut phi_nodes = vec![];

        self.builder.position_at_end(then_br);

        let mut next_br = None;

        if let Some(then_val) = self.gen_tail_expr(env, &cond.consequent) {
            phi_nodes.push((then_val, then_br));

            next_br = Some(parent_func.append("cond_next"));
            self.builder.build_br(next_br.unwrap());
        }

        self.builder.position_at_end(else_br);
        if let Some(else_val) = self.gen_tail_expr(env, &cond.alternative) {
            phi_nodes.push((else_val, else_br));

            if next_br.is_none() {
                next_br = Some(parent_func.append("cond_next"));
            }
            self.builder.build_br(next_br.unwrap());
        }

        if let Some(next_br) = next_br {
            self.builder.position_at_end(next_br);
            Some(self.builder.build_phi(self.gen_type(typ), &phi_nodes))
        } else {
            None
        }
    }

    fn gen_lambda(&self,
                  env: &mut Env<'src, 'ast, 'ctx>,
                  lam: &'ast ast::Lambda<'src>)
                  -> &'ctx Value {
        let anon = self.gen_func_decl("lambda", &lam.get_type());

        self.build_func_def(env, anon, lam);

        anon
    }

    fn gen_var_def<'a>(&self, env: &mut Env<'src, 'ast, 'ctx>, def: &'ast ast::VarDef<'src>) {
        let typ: &'ctx Type = self.gen_type(&def.body.get_type());
        let var: &'ctx Value = self.builder.build_alloca(typ);

        var.set_name(def.binding.s);

        self.builder.build_store(self.gen_expr(env, &def.body), var);

        env.vars.push((def.binding.s, var));
    }

    fn gen_lvalue(&self, env: &mut Env<'src, 'ast, 'ctx>, expr: &'ast Expr<'src>) -> &'ctx Value {
        match *expr {
            Expr::Binding(ref bnd) => {
                env.get_var(bnd.ident.s)
                   .unwrap_or_else(|| expr.pos().error_exit("Invalid assignee expression"))
            }
            _ => expr.pos().error_exit("Invalid assignee expression"),
        }
    }

    fn gen_assign(&self, env: &mut Env<'src, 'ast, 'ctx>, assign: &'ast ast::Assign<'src>) {
        let var = self.gen_lvalue(env, &assign.lhs);

        self.builder.build_store(self.gen_expr(env, &assign.rhs), var);
    }

    fn gen_transmute(&self,
                     env: &mut Env<'src, 'ast, 'ctx>,
                     trans: &'ast ast::Transmute<'src>)
                     -> &'ctx Value {
        let ll_arg = self.gen_expr(env, &trans.arg);

        let ll_arg_typ = ll_arg.get_type();
        let ll_target_typ = self.gen_type(&trans.typ);

        let (arg_size, target_size) = (self.size_of(ll_arg_typ), self.size_of(ll_target_typ));

        if arg_size != target_size {
            trans.pos.error_exit(format!("Transmute to type of different size: {} ({} bytes) to \
                                          {} ({} bytes)",
                                         trans.arg.get_type(),
                                         arg_size,
                                         trans.typ,
                                         target_size))
        }

        if ll_arg_typ == ll_target_typ {
            ll_arg
        } else if ll_arg_typ.is_pointer() && ll_target_typ.is_pointer() {
            self.builder.build_bit_cast(ll_arg, ll_target_typ)
        } else if ll_arg_typ.is_pointer() &&
                  (trans.typ == ast::Type::Basic("IntPtr") ||
                   trans.typ == ast::Type::Basic("UIntPtr")) {
            self.builder.build_ptr_to_int(ll_arg, ll_target_typ)
        } else if ll_arg_typ.is_pointer() {
            let ptr_int = self.builder.build_ptr_to_int(ll_arg, Type::get::<usize>(self.context));

            self.builder.build_bit_cast(ptr_int, ll_target_typ)
        } else if ll_target_typ.is_pointer() &&
                  (*trans.arg.get_type() == ast::Type::Basic("IntPtr") ||
                   *trans.arg.get_type() == ast::Type::Basic("UIntPtr")) {
            self.builder.build_int_to_ptr(ll_arg, ll_target_typ)
        } else if ll_target_typ.is_pointer() {
            let ptr_int = self.builder.build_bit_cast(ll_arg, Type::get::<usize>(self.context));

            self.builder.build_int_to_ptr(ptr_int, ll_target_typ)
        } else {
            self.builder.build_bit_cast(ll_arg, ll_target_typ)
        }
    }

    /// Generate llvm code for an expression and return its llvm Value.
    fn gen_expr(&self, env: &mut Env<'src, 'ast, 'ctx>, expr: &'ast Expr<'src>) -> &'ctx Value {
        match *expr {
            Expr::Nil(_) => self.gen_nil(),
            Expr::NumLit(ref n) => self.gen_num(n),
            Expr::StrLit(ref s) => self.gen_str(s),
            Expr::Bool(ref b) => self.gen_bool(b),
            Expr::Binding(ref bnd) => self.gen_r_binding(env, bnd),
            Expr::Call(ref call) => self.gen_call(env, call),
            Expr::Block(ref block) => self.gen_block(env, block),
            Expr::If(ref cond) => self.gen_if(env, cond, &expr.get_type()),
            Expr::Lambda(ref lam) => self.gen_lambda(env, lam),
            Expr::VarDef(ref def) => {
                self.gen_var_def(env, def);
                self.gen_nil()
            }
            Expr::Assign(ref assign) => {
                self.gen_assign(env, assign);
                self.gen_nil()
            }
            Expr::Transmute(ref trans) => self.gen_transmute(env, trans),
            // All type ascriptions should be replaced at this stage
            Expr::TypeAscript(_) => unreachable!(),
        }
    }

    /// Generate LLVM IR for an expression and return its llvm Value.
    fn gen_tail_expr(&self,
                     env: &mut Env<'src, 'ast, 'ctx>,
                     expr: &'ast Expr<'src>)
                     -> Option<&'ctx Value> {
        match *expr {
            Expr::Call(ref call) => {
                self.gen_tail_call(env, call);
                None
            }
            Expr::Block(ref block) => self.gen_tail_block(env, block),
            Expr::If(ref cond) => self.gen_tail_if(env, cond, &expr.get_type()),
            _ => Some(self.gen_expr(env, expr)),
        }
    }

    /// Generate LLVM IR for a binding to a constant
    fn gen_eval_const_binding(&self,
                              env: &mut Env<'src, 'ast, 'ctx>,
                              bnd: &ast::Binding<'src>)
                              -> &'ctx Value {
        env.statics
           .get(bnd.ident.s)
           .cloned()
           .map(|(_, e)| self.gen_const_expr(env, e))
           .unwrap_or_else(|| bnd.ident.pos.error_exit("binding does not point to constant"))
    }


    fn gen_const_call(&self,
                      env: &mut Env<'src, 'ast, 'ctx>,
                      call: &'ast ast::Call<'src>)
                      -> &'ctx Value {
        let args = call.args
                       .iter()
                       .map(|arg| self.gen_const_expr(env, arg))
                       .collect::<Vec<_>>();

        match call.proced {
            Expr::Binding(ref bnd) if &bnd.ident == "+" => {
                self.builder.build_add(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "-" => {
                self.builder.build_sub(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "*" => {
                self.builder.build_mul(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "/" => {
                self.builder.build_div(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "and" => {
                self.builder.build_and(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "or" => {
                self.builder.build_or(&args[0], &args[1])
            }
            Expr::Binding(ref bnd) if &bnd.ident == "=" => {
                self.builder.build_cmp(&args[0], &args[1], Predicate::Equal)
            }
            Expr::Binding(ref bnd) if &bnd.ident == ">" => {
                self.builder.build_cmp(&args[0], &args[1], Predicate::GreaterThan)
            }
            Expr::Binding(ref bnd) if &bnd.ident == "<" => {
                self.builder.build_cmp(&args[0], &args[1], Predicate::LessThan)
            }
            Expr::Binding(ref bnd) => {
                bnd.ident.pos.error_exit("Binding does not point to a constant function")
            }
            _ => call.pos.error_exit("Non-constant function in constant expression"),
        }
    }

    fn gen_const_expr(&self,
                      env: &mut Env<'src, 'ast, 'ctx>,
                      expr: &'ast Expr<'src>)
                      -> &'ctx Value {
        // TODO: add internal eval over ExprMetas
        match *expr {
            Expr::Nil(_) => self.gen_nil(),
            Expr::NumLit(ref lit) => self.gen_num(lit),
            Expr::StrLit(ref lit) => self.gen_str(lit),
            Expr::Bool(ref b) => self.gen_bool(b),
            Expr::Binding(ref bnd) => self.gen_eval_const_binding(env, bnd),
            Expr::Call(ref call) => self.gen_const_call(env, call),
            _ => expr.pos().error_exit("Expression cannot be used in a constant expression"),
        }
    }

    /// Generate a static
    fn gen_static(&self,
                  env: &mut Env<'src, 'ast, 'ctx>,
                  id: &str,
                  def: &'ast Expr<'src>)
                  -> &'ctx GlobalVariable {
        add_constant_static(&self.module, id, self.gen_const_expr(env, def))
    }

    fn gen_func_decl(&self, id: &str, typ: &ast::Type<'src>) -> &'ctx mut Function {
        self.module.add_function(id, self.gen_type(typ))
    }

    fn build_func_def(&self,
                      env: &mut Env<'src, 'ast, 'ctx>,
                      func: &'ctx Function,
                      def_lam: &'ast ast::Lambda<'src>) {
        *self.building_func.borrow_mut() = Some(func);
        let entry = func.append("entry");

        self.builder.position_at_end(entry);

        let mut param_vars = Vec::with_capacity(def_lam.params.len());

        for (i, param) in def_lam.params.iter().enumerate() {
            let param_var = self.builder.build_alloca(self.gen_type(&param.typ));
            param_var.set_name(param.ident.s);

            self.builder.build_store(&*func[i], param_var);

            param_vars.push((param.ident.s, param_var));
        }

        let old_vars = mem::replace(&mut env.vars, param_vars);

        if let Some(e) = self.gen_tail_expr(env, &def_lam.body) {
            self.builder.build_ret(e);
        }

        env.vars = old_vars;
        *self.building_func.borrow_mut() = None;
    }

    pub fn gen_extern_decls(&self,
                            env: &mut Env<'src, 'ast, 'ctx>,
                            extern_funcs: &HashMap<&'src str, ast::ExternProcDecl<'src>>) {
        let mut func_decls = HashMap::new();

        for (id, typ) in extern_funcs.iter().map(|(id, decl)| (*id, &decl.typ)) {
            func_decls.insert(id, self.gen_func_decl(id, typ) as &_);
        }

        env.funcs.push(func_decls);
    }

    pub fn gen_static_defs(&self,
                           env: &mut Env<'src, 'ast, 'ctx>,
                           static_defs: &'ast HashMap<&'src str, ast::StaticDef<'src>>) {
        let (mut func_decls, mut static_decls) = (HashMap::new(), HashMap::new());
        // function declarations that are to be defined
        let (mut undef_funcs, mut undef_statics) = (Vec::new(), Vec::new());

        for (&id, static_def) in static_defs.iter() {
            match static_def.body {
                Expr::Lambda(ref lam) => {
                    let func: &_ = self.gen_func_decl(id, &lam.get_type());
                    func_decls.insert(id, func);
                    undef_funcs.push((func, lam));
                }
                _ => {
                    // Declare statics
                    let undef_glob = self.module
                                         .add_global(id,
                                                     self.gen_type(&*static_def.body.get_type()));
                    static_decls.insert(id, (undef_glob, &static_def.body));
                    undef_statics.push(id);
                }
            }
        }

        env.statics.push(static_decls);

        for id in undef_statics {
            let def = env.statics.get(id).unwrap().1;
            let static_val = self.gen_static(env, id, def);
            let undef = &mut env.statics.get_mut(id).unwrap().0;

            *undef = static_val;
        }

        env.funcs.push(func_decls);

        for (func, def_lam) in undef_funcs {
            self.build_func_def(env, func, def_lam);
        }
    }
}
