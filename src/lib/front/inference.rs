//! Type inference

// TODO: Almost all `infer_types` takes const map + var stack + caller stack.
//       Maybe encapsulate this using some kind of state
// TODO: Replace verbose type error checks with:
//       `foo.infer_types(...)
//           .unwrap_or_else(foo.pos().type_mismatcher(expected_ty))`

use self::InferenceErr::*;
use lib::collections::ScopeStack;
use lib::front::ast::*;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::{self, Display};
use std::mem::{replace, swap};

enum InferenceErr<'p, 'src: 'p> {
    /// Type mismatch. (expected, found)
    TypeMis(&'p Type<'src>, &'p Type<'src>),
    ArmsDiffer(&'p Type<'src>, &'p Type<'src>),
}
impl<'src, 'p> Display for InferenceErr<'src, 'p> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeMis(expected, found) => {
                write!(f,
                       "Type mismatch. Expected `{}`, found `{}`",
                       expected,
                       found)
            }
            ArmsDiffer(c, a) => {
                write!(f,
                       "Consequent and alternative have different types. Expected `{}` from \
                        alternative, found `{}`",
                       c,
                       a)
            }
        }
    }
}

struct Inferer<'src> {
    vars: Vec<(&'src str, Type<'src>)>,
    static_defs: ScopeStack<&'src str, Option<StaticDef<'src>>>,
    extern_funcs: ScopeStack<&'src str, ExternProcDecl<'src>>,
}
impl<'src> Inferer<'src> {
    fn new(ast: &mut Module<'src>) -> Self {
        let mut static_defs = ScopeStack::new();
        static_defs.push(replace(&mut ast.static_defs, HashMap::new())
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect());

        let mut extern_funcs = ScopeStack::new();
        extern_funcs.push(replace(&mut ast.extern_funcs, HashMap::new()));

        Inferer {
            vars: Vec::new(),
            static_defs: static_defs,
            extern_funcs: extern_funcs,
        }
    }

    fn into_inner
        (mut self)
         -> (HashMap<&'src str, StaticDef<'src>>, HashMap<&'src str, ExternProcDecl<'src>>) {
        let static_defs =
            self.static_defs
                .pop()
                .expect("ICE: Inferer::into_inner: static_defs.pop() failed")
                .into_iter()
                .map(|(k, v)| {
                    (k, v.expect("ICE: Inferer::into_inner: None when unmapping const def"))
                })
                .collect();
        let extern_funcs = self.extern_funcs
                               .pop()
                               .expect("ICE: Inferer::into_inner: extern_funcs.pop() failed");

        (static_defs, extern_funcs)
    }

    fn get_var_type_mut(&mut self, id: &str) -> Option<&mut Type<'src>> {
        self.vars.iter_mut().rev().find(|&&mut (b, _)| b == id).map(|&mut (_, ref mut t)| t)
    }

    fn infer_static_def(&mut self,
                        def: &mut StaticDef<'src>,
                        expected_ty: &Type<'src>)
                        -> Type<'src> {
        self.infer_expr(&mut def.body, expected_ty)
    }

    fn infer_nil(&mut self, nil: &mut Nil<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        if let Some(type_nil) = expected_ty.infer_by(&TYPE_NIL) {
            type_nil
        } else {
            nil.pos.error_exit(TypeMis(expected_ty, &TYPE_NIL))
        }
    }

    fn infer_num_lit(&mut self, lit: &mut NumLit<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        match *expected_ty {
            Type::Unknown |
            Type::Basic("Int8") |
            Type::Basic("UInt8") |
            Type::Basic("Int16") |
            Type::Basic("UInt16") |
            Type::Basic("Int32") |
            Type::Basic("UInt32") |
            Type::Basic("Float32") |
            Type::Basic("Int64") |
            Type::Basic("UInt64") |
            Type::Basic("Float64") |
            Type::Basic("IntPtr") |
            Type::Basic("UIntPtr") => {
                lit.typ = expected_ty.clone();
                expected_ty.clone()
            }
            _ => {
                lit.pos.error_exit(format!("Type mismatch. Expected `{}`, found numeric literal",
                                           expected_ty))
            }
        }
    }

    fn infer_str_lit(&mut self, lit: &mut StrLit<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        if expected_ty.infer_by(&TYPE_BYTE_SLICE).is_some() {
            lit.typ = TYPE_BYTE_SLICE.clone();
            TYPE_BYTE_SLICE.clone()
        } else {
            lit.pos.error_exit(TypeMis(expected_ty, &TYPE_BYTE_SLICE))
        }
    }

    fn infer_bool(&mut self, b: &mut Bool<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        if expected_ty.infer_by(&TYPE_BOOL).is_some() {
            TYPE_BOOL.clone()
        } else {
            b.pos.error_exit(TypeMis(expected_ty, &TYPE_BOOL))
        }
    }

    fn infer_binding(&mut self, bnd: &mut Binding<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        // In order to not violate any borrowing rules, use get_height to check if entry exists
        // and to speed up upcoming lookup
        if let Some(height) = self.extern_funcs.get_height(bnd.ident.s) {
            // Don't infer types for external items,
            // just check compatibility with expected_ty

            let extern_typ = &self.extern_funcs.get_at_height(bnd.ident.s, height).unwrap().typ;
            if let Some(inferred) = extern_typ.infer_by(expected_ty) {
                bnd.typ = inferred.clone();
                inferred
            } else {
                bnd.ident.pos.error_exit(TypeMis(expected_ty, &extern_typ))
            }
        } else if let Some(height) = self.static_defs.get_height(bnd.ident.s) {
            // Binding is a constant. Do inference

            let maybe_def =
                replace(self.static_defs.get_at_height_mut(bnd.ident.s, height).unwrap(),
                        None);

            if let Some(mut def) = maybe_def {
                let old_vars = replace(&mut self.vars, Vec::new());

                let inferred = self.infer_static_def(&mut def, expected_ty);

                self.vars = old_vars;
                self.static_defs.update(bnd.ident.s, Some(def));
                bnd.typ = inferred.clone();

                inferred
            } else {
                // We are currently doing inference inside this definition, and as such
                // no more type information can be given for sure than Unknown

                Type::Unknown
            }
        } else if let Some(var_ty) = self.get_var_type_mut(bnd.ident.s) {
            // Binding is a variable

            if let Some(inferred) = var_ty.infer_by(expected_ty) {
                *var_ty = inferred.clone();
                bnd.typ = inferred.clone();
                inferred
            } else {
                bnd.ident.pos.error_exit(TypeMis(expected_ty, var_ty))
            }
        } else {
            bnd.ident.pos.error_exit(format!("Unresolved path `{}`", bnd.ident))
        }
    }

    fn infer_call_arg_types(&mut self, call: &mut Call<'src>) {
        let proc_type = call.proced.get_type();

        let expected_types: Vec<&Type> = if proc_type.is_partially_known() {
            // The type of the procedure is not unknown.
            // If it's a valid procedure type, use it for inference

            match proc_type.get_proc_sig() {
                Some((param_tys, _)) if param_tys.len() == call.args.len() => {
                    param_tys.iter().collect()
                }
                Some((param_tys, _)) => {
                    call.pos.error_exit(format!("Arity mismatch. Expected {}, found {}",
                                                param_tys.len(),
                                                call.args.len()))
                }
                None => {
                    call.proced
                        .pos()
                        .error_exit(TypeMis(&Type::new_proc(vec![Type::Unknown], Type::Unknown),
                                            &proc_type))
                }
            }
        } else {
            vec![call.proced.get_type(); call.args.len()]
        };

        for (arg, expect_ty) in call.args.iter_mut().zip(expected_types) {
            self.infer_expr(arg, &expect_ty);
        }
    }

    fn infer_call<'call>(&mut self,
                         call: &'call mut Call<'src>,
                         expected_ty: &Type<'src>)
                         -> &'call Type<'src> {
        self.infer_call_arg_types(call);

        let expected_proc_type = Type::new_proc(call.args
                                                    .iter()
                                                    .map(|arg| arg.get_type().clone())
                                                    .collect(),
                                                expected_ty.clone());

        let old_proc_typ = call.proced.get_type().clone();

        let proc_typ = self.infer_expr(&mut call.proced, &expected_proc_type);

        // TODO: This only works for function pointers, i.e. lambdas will need some different type.
        //       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

        if old_proc_typ != proc_typ {
            // New type information regarding arg types available
            self.infer_call_arg_types(call);
        }

        call.typ = call.proced
                       .get_type()
                       .get_proc_sig()
                       .map(|(_, ret_typ)| ret_typ.clone())
                       .unwrap_or(Type::Unknown);

        &call.typ
    }

    fn infer_block(&mut self, block: &mut Block<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        let (init, last) = if let Some((last, init)) = block.exprs.split_last_mut() {
            (init, last)
        } else {
            return TYPE_NIL.clone();
        };

        self.static_defs.push(replace(&mut block.static_defs, HashMap::new())
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect());

        let old_vars_len = self.vars.len();

        // First pass. If possible, all vars defined in block should have types inferred.
        for expr in init.iter_mut() {
            if let Expr::VarDef(ref mut var_def) = *expr {
                self.infer_var_def(var_def, &Type::Unknown);
                self.vars.push((var_def.binding.s, var_def.body.get_type().clone()));
            } else {
                self.infer_expr(expr, &Type::Unknown);
            }
        }

        self.infer_expr(last, expected_ty);

        let mut block_defined_vars = self.vars.split_off(old_vars_len).into_iter();

        // Second pass. Infer types for all expressions in block now that types for all bindings
        // are, if possible, known.
        for expr in init {
            if let Expr::VarDef(ref mut var_def) = *expr {
                let v = block_defined_vars.next().expect("ICE: block_defined_vars empty");

                self.infer_expr(&mut var_def.body, &v.1);

                self.vars.push(v);
            } else {
                self.infer_expr(expr, &Type::Unknown);
            }
        }
        let last_typ = self.infer_expr(last, expected_ty);

        self.vars.truncate(old_vars_len);

        block.static_defs =
            self.static_defs
                .pop()
                .expect("ICE: ScopeStack was empty when replacing Block const defs")
                .into_iter()
                .map(|(k, v)| (k, v.expect("ICE: None when unmapping block const def")))
                .collect();

        last_typ
    }

    fn infer_if(&mut self, cond: &mut If<'src>, expected_typ: &Type<'src>) -> Type<'src> {
        self.infer_expr(&mut cond.predicate, &TYPE_BOOL);

        let cons_typ = self.infer_expr(&mut cond.consequent, expected_typ);
        let alt_typ = self.infer_expr(&mut cond.alternative, expected_typ);

        if let Some(inferred) = cons_typ.infer_by(&alt_typ) {
            let cons_typ = self.infer_expr(&mut cond.consequent, &inferred);
            let alt_typ = self.infer_expr(&mut cond.alternative, &inferred);

            if cons_typ == inferred && alt_typ == inferred { inferred } else { Type::Unknown }
        } else {
            cond.pos.error_exit(ArmsDiffer(&cons_typ, &alt_typ))
        }
    }

    fn infer_lambda_args(&mut self, lam: &mut Lambda<'src>, expected_params: &[&Type<'src>]) {
        for (param, expected_param) in lam.params.iter_mut().zip(expected_params) {
            match param.typ.infer_by(expected_param) {
                Some(inferred) => param.typ = inferred,
                None => param.ident.pos.error_exit(TypeMis(expected_param, &param.typ)),
            }
        }
    }

    fn infer_lambda<'l>(&mut self,
                        lam: &'l mut Lambda<'src>,
                        expected_ty: &Type<'src>)
                        -> &'l Type<'src> {
        let (expected_params, expected_body) = match expected_ty.get_proc_sig() {
            Some((params, _)) if params.len() != lam.params.len() => {
                lam.pos.error_exit(TypeMis(expected_ty, &lam.typ))
            }
            Some((params, body)) => (params.iter().collect(), body),
            None if *expected_ty == Type::Unknown => {
                (vec![expected_ty; lam.params.len()], expected_ty)
            }
            None => lam.pos.error_exit(TypeMis(expected_ty, &lam.typ)),
        };

        // Own type is `Unknown` if no type has been inferred yet, or none was inferable

        if lam.typ.is_partially_known() {
            if let Some(inferred) = expected_ty.infer_by(&lam.typ) {
                if lam.typ == inferred {
                    // Own type can't be inferred further by `expected_ty`
                    return &lam.typ;
                }
            } else {
                // Own type and expected type are not compatible. Type mismatch
                lam.pos.error_exit(TypeMis(expected_ty, &lam.typ));
            }
        }

        self.infer_lambda_args(lam, &expected_params);

        let (vars_len, n_params) = (self.vars.len(), lam.params.len());

        self.vars.extend(lam.params.iter().cloned().map(|param| (param.ident.s, param.typ)));

        self.infer_expr(&mut lam.body, &expected_body);

        assert_eq!(self.vars.len(), vars_len + n_params);

        for (param, found) in lam.params
                                 .iter_mut()
                                 .zip(self.vars.drain(vars_len..))
                                 .map(|(param, (_, found))| (&mut param.typ, found)) {
            *param = found;
        }

        lam.typ = Type::new_proc(lam.params.iter().map(|p| p.typ.clone()).collect(),
                                 lam.body.get_type().clone());
        &lam.typ
    }

    fn infer_var_def(&mut self, def: &mut VarDef<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        if let Some(inferred) = expected_ty.infer_by(&TYPE_NIL) {
            self.infer_expr(&mut def.body, &Type::Unknown);
            def.typ = inferred.clone();
            inferred
        } else {
            def.pos.error_exit(TypeMis(expected_ty, &TYPE_NIL))
        }
    }

    fn infer_assign(&mut self, assign: &mut Assign<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        if let Some(inferred) = expected_ty.infer_by(&TYPE_NIL) {
            let rhs_typ = self.infer_expr(&mut assign.rhs, &assign.lhs.get_type());
            self.infer_expr(&mut assign.lhs, &rhs_typ);
            inferred
        } else {
            assign.pos.error_exit(TypeMis(expected_ty, &TYPE_NIL))
        }
    }

    fn infer_transmute<'ast>(&mut self,
                             trans: &'ast mut Transmute<'src>,
                             expected_ty: &Type<'src>)
                             -> &'ast Type<'src> {
        if let Some(inferred) = trans.typ.infer_by(expected_ty) {
            trans.typ = inferred;

            self.infer_expr(&mut trans.arg, &Type::Unknown);

            &trans.typ
        } else {
            trans.pos.error_exit(TypeMis(expected_ty, &trans.typ))
        }
    }

    fn infer_type_ascript(&mut self,
                          expr: &mut Expr<'src>,
                          expected_ty: &Type<'src>)
                          -> Type<'src> {
        let (expected_ty2, inner_expr) = if let Expr::TypeAscript(ref mut ascr) = *expr {
            let expected_ty2 =
                expected_ty.infer_by(&ascr.typ)
                           .unwrap_or_else(|| ascr.pos.error_exit(TypeMis(expected_ty, &ascr.typ)));

            (expected_ty2, &mut ascr.expr as *mut _)
        } else {
            // This method should only be called when `expr` is a type ascription
            unreachable!()
        };

        // FIXME: Safe way of conducting this replacement
        unsafe { swap(expr, &mut *inner_expr) };

        self.infer_expr(expr, &expected_ty2)
    }

    fn infer_expr(&mut self, expr: &mut Expr<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        let mut expected_ty = Cow::Borrowed(expected_ty);

        {
            let expr_typ = expr.get_type();

            // Own type is `Unknown` if no type has been inferred yet, or none was inferable
            if expr_typ.is_partially_known() {
                if let Some(inferred) = expected_ty.infer_by(&expr_typ) {
                    if *expr_typ == inferred {
                        // Own type can't be inferred further by `expected_ty`
                        return expr_typ.clone();
                    }
                    expected_ty = Cow::Owned(inferred)
                } else {
                    // Own type and expected type are not compatible. Type mismatch
                    expr.pos().error_exit(TypeMis(&expected_ty, &expr_typ));
                }
            }
        }

        // Own type is unknown, or `expected_ty` is more known than own type. Do inference

        match *expr {
            Expr::Nil(ref mut nil) => self.infer_nil(nil, &expected_ty),
            Expr::VarDef(ref mut def) => self.infer_var_def(def, &expected_ty),
            Expr::Assign(ref mut assign) => self.infer_assign(assign, &expected_ty),
            Expr::NumLit(ref mut l) => self.infer_num_lit(l, &expected_ty),
            Expr::StrLit(ref mut l) => self.infer_str_lit(l, &expected_ty),
            Expr::Bool(ref mut b) => self.infer_bool(b, &expected_ty),
            Expr::Binding(ref mut bnd) => self.infer_binding(bnd, &expected_ty),
            Expr::Call(ref mut call) => self.infer_call(call, &expected_ty).clone(),
            Expr::Block(ref mut block) => self.infer_block(block, &expected_ty),
            Expr::If(ref mut cond) => self.infer_if(cond, &expected_ty),
            Expr::Lambda(ref mut lam) => self.infer_lambda(lam, &expected_ty).clone(),
            Expr::Transmute(ref mut trans) => self.infer_transmute(trans, &expected_ty).clone(),
            Expr::TypeAscript(_) => self.infer_type_ascript(expr, &expected_ty),
        }
    }
}

pub fn infer_types(ast: &mut Module) {
    let mut inferer = Inferer::new(ast);

    let mut main = replace(inferer.static_defs
                                  .get_mut("main")
                                  .expect("ICE: In infer_ast: No main def"),
                           None)
                       .unwrap();

    inferer.infer_static_def(&mut main, &Type::new_proc(vec![], Type::Basic("Int64")));

    inferer.static_defs.update("main", Some(main));

    let (static_defs, extern_funcs) = inferer.into_inner();

    ast.static_defs = static_defs;
    ast.extern_funcs = extern_funcs;
}
