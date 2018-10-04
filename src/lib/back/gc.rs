//! Interface to the garbage collector

use lib::front::ast;
use std::collections::BTreeMap;
use super::llvm::*;
use super::codegen::*;

pub struct Gc<'ctx, 'src> {
    ctx: &'ctx Context,
    builder: &'ctx Builder,
    pub obj_visitors: BTreeMap<ast::Type<'src>, Option<&'ctx Function>>,
    pub adt_obj_visitors: BTreeMap<(&'src str, Vec<ast::Type<'src>>), &'ctx Function>,
    pub captures_obj_visitors: BTreeMap<Vec<ast::Type<'src>>, Option<&'ctx Function>>,
    push_new_scope: &'ctx Function,
    alloc_temp: &'ctx Function,
    mark_bound: &'ctx Function,
    mark_bound_and_clear_scope_temps: &'ctx Function,
    pop_scope: &'ctx Function,
    update_obj_visitor: &'ctx Function,
    move_locals_to_parent_scope_as_temps_and_pop_scope: &'ctx Function,
    pub closure_obj_visitor: &'ctx Function,
    pub handle_self_obj_visitor: &'ctx Function,
    pub nop_obj_visitor: &'ctx Function,
    pub obj_visitor_type: &'ctx Type,
}

impl<'ctx, 'src> Gc<'ctx, 'src> {
    pub fn new(ctx: &'ctx Context, module: &'ctx Module, builder: &'ctx Builder) -> Self {
        // type ObjHandler = extern "C" fn(obj_ref: *mut i8);
        // type ObjVisitor = extern "C" fn(obj: *mut i8, Obj_handler: ObjHandler);
        // extern "C" fn gc_alloc(size: usize, Obj_visitor: ObjVisitor) -> *mut i8;
        let t_usize = CodeGenerator::gen_int_ptr_type(module, ctx);
        let t_i8 = Type::get::<i8>(ctx);
        let t_ptr_i8 = PointerType::new(t_i8);
        let t_void = Type::get::<()>(ctx);
        let t_obj_handler = PointerType::new(FunctionType::new(t_void, &[t_ptr_i8]));
        let t_obj_visitor = FunctionType::new(t_void, &[t_ptr_i8, t_obj_handler]);
        let obj_visitor_type = t_obj_visitor;
        let alloc_type = FunctionType::new(t_ptr_i8, &[t_usize, t_obj_visitor]);
        let alloc_temp = module.add_function("gc_alloc", alloc_type);
        let closure_obj_visitor =
            Gc::gen_closure_obj_visitor(ctx, module, builder, obj_visitor_type);
        let handle_self_obj_visitor =
            Gc::gen_handle_self_obj_visitor(module, builder, obj_visitor_type);
        let t_void = Type::get::<()>(ctx);
        let mark_bound_type = FunctionType::new(t_void, &[t_ptr_i8, t_obj_visitor]);
        let mark_bound = module.add_function("gc_mark_bound", mark_bound_type);
        let mark_bound_and_clear_scope_temps =
            module.add_function("gc_mark_bound_and_clear_scope_temps", mark_bound_type);
        let nop_obj_visitor = Gc::gen_nop_obj_visitor(module, builder, t_obj_visitor);
        let pop_scope = module.add_function("gc_pop_scope", FunctionType::new(t_void, &[]));
        let push_new_scope =
            module.add_function("gc_push_new_scope", FunctionType::new(t_void, &[]));
        let update_obj_visitor = module.add_function(
            "gc_update_obj_visitor",
            FunctionType::new(t_void, &[t_ptr_i8, t_obj_visitor]),
        );
        let move_locals_to_parent_scope_as_temps_and_pop_scope = module.add_function(
            "gc_move_locals_to_parent_scope_as_temps_and_pop_scope",
            FunctionType::new(t_void, &[]),
        );
        Gc {
            ctx,
            builder,
            alloc_temp,
            closure_obj_visitor,
            obj_visitor_type,
            adt_obj_visitors: BTreeMap::new(),
            captures_obj_visitors: BTreeMap::new(),
            handle_self_obj_visitor,
            mark_bound,
            mark_bound_and_clear_scope_temps,
            nop_obj_visitor,
            obj_visitors: BTreeMap::new(),
            pop_scope,
            push_new_scope,
            update_obj_visitor,
            move_locals_to_parent_scope_as_temps_and_pop_scope,
        }
    }

    fn gen_closure_obj_visitor(
        ctx: &'ctx Context,
        module: &'ctx Module,
        builder: &'ctx Builder,
        obj_visitor_type: &'ctx Type,
    ) -> &'ctx Function {
        let func = module.add_function("obj_visitor_closure", obj_visitor_type);
        let entry = func.append("entry");
        builder.position_at_end(entry);
        let closure_generic_ptr = &*func[0];
        let t_generic_ptr = PointerType::new(Type::get::<u8>(ctx));
        let t_func_ptr = t_generic_ptr;
        let t_captures = t_generic_ptr;
        let t_closure = StructType::new(ctx, &[t_func_ptr, t_captures], false);
        let t_closure_ptr = PointerType::new(t_closure);
        let closure_ptr = builder.build_bit_cast(closure_generic_ptr, t_closure_ptr);
        let captures_ptr = builder.build_gep_struct(ctx, closure_ptr, 1);
        let captures = builder.build_load(captures_ptr);
        captures.set_name("captures");
        let obj_handler = Function::from_super(&*func[1])
            .expect("ICE: obj_handler was not a function in gen_closure_obj_visitor");
        obj_handler.set_name("obj_handler");
        builder.build_call(obj_handler, &[captures]);
        func
    }

    fn gen_handle_self_obj_visitor(
        module: &'ctx Module,
        builder: &'ctx Builder,
        obj_visitor_type: &'ctx Type,
    ) -> &'ctx Function {
        let func = module.add_function("obj_visitor_handle_self", obj_visitor_type);
        let entry = func.append("entry");
        builder.position_at_end(entry);
        let obj = &*func[0];
        obj.set_name("self");
        let obj_handler = &*func[1];
        obj_handler.set_name("obj_handler");
        builder.build_call(Function::from_super(obj_handler).unwrap(), &[obj]);
        func
    }

    fn gen_nop_obj_visitor(
        module: &'ctx Module,
        builder: &'ctx Builder,
        obj_visitor_type: &'ctx Type,
    ) -> &'ctx Function {
        let func = module.add_function("obj_visitor_nop", obj_visitor_type);
        let entry = func.append("entry");
        builder.position_at_end(entry);
        func
    }

    pub fn build_alloc_temp(&self, size: usize, obj_visitor: &'ctx Function) -> &'ctx Value {
        self.builder
            .build_call(self.alloc_temp, &[size.compile(self.ctx), obj_visitor])
    }

    pub fn build_push_new_scope(&self) {
        self.builder.build_call(self.push_new_scope, &[]);
    }

    pub fn build_mark_bound(&self, obj: &Value, obj_visitor: &Function) {
        self.builder
            .build_call(self.mark_bound, &[obj, obj_visitor]);
    }

    pub fn build_pop_scope(&self) {
        self.builder.build_call(self.pop_scope, &[]);
    }

    pub fn build_update_obj_visitor(&self, captures_ptr: &Value, obj_visitor: &Function) {
        self.builder
            .build_call(self.update_obj_visitor, &[captures_ptr, obj_visitor]);
    }

    pub fn build_mark_bound_and_clear_scope_temps(&self, obj: &Value, obj_visitor: &Function) {
        self.builder
            .build_call(self.mark_bound_and_clear_scope_temps, &[obj, obj_visitor]);
    }

    pub fn build_move_locals_to_parent_scope_as_temps_and_pop_scope(&self) {
        self.builder
            .build_call(self.move_locals_to_parent_scope_as_temps_and_pop_scope, &[]);
    }
}
