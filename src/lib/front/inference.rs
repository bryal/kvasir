//! Type inference

// TODO: Almost all `infer_types` takes const map + var stack + caller stack.
//       Maybe encapsulate this using some kind of state
// TODO: Replace verbose type error checks with:
//       `foo.infer_types(...)
//           .unwrap_or_else(foo.pos().type_mismatcher(expected_ty))`
// TODO: Encode whether types have been inferred in the type of the
//       AST. E.g. `type InferredAst = Ast<Ty = Type>; type UninferredAst = Ast<Ty = Option<Type>>`

use self::InferenceErr::*;
use lib::collections::ScopeStack;
use lib::front::ast::*;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::{self, Display};
use std::mem::{replace, swap};

/// Instantiate the type scheme of `vars` and `poly` with `t`
///
/// If `t` is not consistent with the signature, not counting conflicting type
/// variables, return `None`.
///
/// # Example
/// ```
/// (forall a,b,c in (instantiate (forall a in (Tuple a a a c)) (Tuple a b int int)))
///     = (Tuple int int int c)
/// ```
fn instantiate<'src>(vars: &mut HashMap<u64, Type<'src>>,
                     poly: &Type<'src>,
                     t: &Type<'src>)
                     -> Option<Type<'src>> {
    /// Substitute parts or the whole of the constraint for more specialized parts
    /// in `special`.
    ///
    /// If `special` is not consistent with the constraint, not counting conflicting
    /// type variables, return `None`
    fn specialize_constraint<'src>(constraint: &Type<'src>,
                                   special: &Type<'src>)
                                   -> Option<Type<'src>> {
        match (constraint, special) {
            (_, _) if constraint == special => Some(constraint.clone()),
            (&Type::Uninferred, _) => Some(special.clone()),
            (_, &Type::Uninferred) => Some(constraint.clone()),
            (&Type::Var(a), &Type::Var(b)) if a < b => Some(Type::Var(a)),
            (&Type::Var(_), _) => Some(special.clone()),
            (&Type::App(s1, ref as1), &Type::App(s2, ref as2)) if s1 == s2 => {
                as1.iter()
                   .zip(as2)
                   .map(|(a1, a2)| specialize_constraint(a1, a2))
                   .collect::<Option<_>>()
                   .map(|args| Type::App(s1, args))
            }
            (_, _) => None,
        }
    }

    /// Gather constraints for the type variables `vars` from the most special types of `t`
    fn gather_constraints<'src>(vars: &mut HashMap<u64, Type<'src>>,
                                poly: &Type<'src>,
                                t: &Type<'src>)
                                -> Result<(), ()> {
        match (poly, t) {
            (&Type::Var(ref id), _) if vars.contains_key(id) => {
                match specialize_constraint(&vars[id], t) {
                    Some(c) => {
                        vars.insert(*id, c);
                        Ok(())
                    }
                    None => Err(()),
                }
            }
            (&Type::App(s1, ref as1), &Type::App(s2, ref as2)) if s1 == s2 => {
                as1.iter()
                   .zip(as2)
                   .map(|(a1, a2)| gather_constraints(vars, a1, a2))
                   .fold(Ok(()), |acc, r| acc.and(r))
            }
            (&Type::Scheme(_, _), _) |
            (_, &Type::Scheme(_, _)) => panic!("ICE: Type scheme encountered during \
                                                `gather_constraints`"),
            (_, _) => Ok(()),
        }
    }

    /// Apply the substitutions from type variables to inferred and constrained
    /// types of `substs` to the relevant type variables in `poly`
    fn substitute<'src>(substs: &HashMap<u64, Type<'src>>, poly: &Type<'src>) -> Type<'src> {
        match *poly {
            Type::Var(ref id) if substs.contains_key(id) => substs[id].clone(),
            Type::App(s, ref args) => Type::App(s,
                                                args.iter()
                                                    .map(|arg| substitute(substs, arg))
                                                    .collect()),
            Type::Scheme(_, _) => panic!("ICE: Type scheme encountered during `substitute`"),
            _ => poly.clone(),
        }
    }

    match gather_constraints(vars, poly, t) {
        Ok(()) => Some(substitute(vars, poly)),
        Err(()) => None,
    }
}

enum InferenceErr<'p, 'src: 'p> {
    /// Type mismatch. (expected, found)
    TypeMis(&'p Type<'src>, &'p Type<'src>),
    ArmsDiffer(&'p Type<'src>, &'p Type<'src>),
    NonNilNullary(&'p Type<'src>),
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
            NonNilNullary(t) => write!(f,
                                       "Infering non-nil type `{}` for the parameter of a \
                                        nullary function",
                                       t),
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
        let vars = replace(&mut self.vars, Vec::new());

        let inferred = self.infer_expr(&mut def.body, expected_ty);

        self.vars = vars;

        inferred
    }

    fn infer_nil(&mut self, nil: &mut Nil<'src>, expected_type: &Type<'src>) -> Type<'src> {
        if let Some(type_nil) = expected_type.infer_by(&TYPE_NIL) {
            type_nil
        } else {
            nil.pos.error_exit(TypeMis(expected_type, &TYPE_NIL))
        }
    }

    fn infer_num_lit(&mut self, lit: &mut NumLit<'src>, expected_type: &Type<'src>) -> Type<'src> {
        match *expected_type {
            Type::Uninferred |
            Type::Const("Int8") |
            Type::Const("UInt8") |
            Type::Const("Int16") |
            Type::Const("UInt16") |
            Type::Const("Int32") |
            Type::Const("UInt32") |
            Type::Const("Float32") |
            Type::Const("Int64") |
            Type::Const("UInt64") |
            Type::Const("Float64") |
            Type::Const("IntPtr") |
            Type::Const("UIntPtr") => {
                lit.typ = expected_type.clone();
                expected_type.clone()
            }
            _ => {
                lit.pos.error_exit(format!("Type mismatch. Expected `{}`, found numeric literal",
                                           expected_type))
            }
        }
    }

    fn infer_str_lit(&mut self, lit: &mut StrLit<'src>, expected_type: &Type<'src>) -> Type<'src> {
        if expected_type.infer_by(&TYPE_BYTE_SLICE).is_some() {
            lit.typ = TYPE_BYTE_SLICE.clone();
            TYPE_BYTE_SLICE.clone()
        } else {
            lit.pos.error_exit(TypeMis(expected_type, &TYPE_BYTE_SLICE))
        }
    }

    fn infer_bool(&mut self, b: &mut Bool<'src>, expected_type: &Type<'src>) -> Type<'src> {
        if expected_type.infer_by(&TYPE_BOOL).is_some() {
            TYPE_BOOL.clone()
        } else {
            b.pos.error_exit(TypeMis(expected_type, &TYPE_BOOL))
        }
    }

    fn infer_binding(&mut self, bnd: &mut Binding<'src>, expected_type: &Type<'src>) -> Type<'src> {
        if self.get_var_type_mut(bnd.ident.s).is_some() {
            // Binding is a variable

            let var_type = self.get_var_type_mut(bnd.ident.s).unwrap();

            if let Some(inferred) = var_type.infer_by(expected_type) {
                *var_type = inferred.clone();
                bnd.typ = inferred.clone();
                inferred
            } else {
                bnd.ident.pos.error_exit(TypeMis(expected_type, var_type))
            }
        } else if let Some(height) = self.extern_funcs.get_height(bnd.ident.s) {
            // Don't infer types for external items,
            // just check compatibility with expected_type

            let extern_type = &self.extern_funcs.get_at_height(bnd.ident.s, height).unwrap().typ;
            if let Some(inferred) = extern_type.infer_by(expected_type) {
                bnd.typ = inferred.clone();
                inferred
            } else {
                bnd.ident.pos.error_exit(TypeMis(expected_type, &extern_type))
            }
        } else if let Some(height) = self.static_defs.get_height(bnd.ident.s) {
            // Binding is a constant. Do inference

            let maybe_def =
                replace(self.static_defs.get_at_height_mut(bnd.ident.s, height).unwrap(),
                        None);

            if let Some(mut def) = maybe_def {
                // The definition is available, do inference

                let inferred = self.infer_static_def(&mut def, expected_type);
                self.static_defs.update(bnd.ident.s, Some(def));
                bnd.typ = inferred.clone();

                inferred
            } else {
                // We are already inferring the type of this definition,
                // i.e. it's a recursive definition

                unimplemented!()
            }
        } else {
            bnd.ident.pos.error_exit(format!("Unresolved path `{}`", bnd.ident))
        }
    }

    fn infer_call_arg(&mut self, call: &mut Call<'src>) {
        let func_type = call.func.get_type();

        let expected_typ: &Type = if func_type.is_partially_known() {
            &func_type.get_func_sig().unwrap_or_else(|| unreachable!()).0
        } else {
            &TYPE_UNINFERRED
        };

        if let Some(ref mut arg) = call.arg {
            self.infer_expr(arg, expected_typ);
        }
    }

    // 1. Infer function and arg types independently
    // 2. Instantiate function for the most specialized args
    // 3. Attempt to unify the function type and the argument types
    //    by specializing polytypes
    fn infer_call<'call>(&mut self,
                         call: &'call mut Call<'src>,
                         expected_ty: &Type<'src>)
                         -> &'call Type<'src> {
        self.infer_call_arg(call);

        let arg_typ = call.arg.as_ref().map(|arg| arg.get_type()).unwrap_or(&TYPE_NIL).clone();
        let expected_func_type = Type::new_func(arg_typ, expected_ty.clone());

        let old_func_typ = call.func.get_type().clone();

        let func_typ = self.infer_expr(&mut call.func, &expected_func_type);

        // TODO: This only works for function pointers, i.e. lambdas will need some different type.
        //       When traits are added, use a function trait like Rusts Fn/FnMut/FnOnce

        if old_func_typ != func_typ {
            // New type information regarding arg types available
            self.infer_call_arg(call);
        }

        call.typ = call.func
                       .get_type()
                       .get_func_sig()
                       .map(|(_, ret_typ)| ret_typ.clone())
                       .unwrap_or(Type::Uninferred);

        &call.typ
    }

    fn infer_if(&mut self, cond: &mut If<'src>, expected_typ: &Type<'src>) -> Type<'src> {
        self.infer_expr(&mut cond.predicate, &TYPE_BOOL);

        let cons_typ = self.infer_expr(&mut cond.consequent, expected_typ);
        let alt_typ = self.infer_expr(&mut cond.alternative, expected_typ);

        if let Some(inferred) = cons_typ.infer_by(&alt_typ) {
            let cons_typ = self.infer_expr(&mut cond.consequent, &inferred);
            let alt_typ = self.infer_expr(&mut cond.alternative, &inferred);

            if cons_typ == inferred && alt_typ == inferred { inferred } else { Type::Uninferred }
        } else {
            cond.pos.error_exit(ArmsDiffer(&cons_typ, &alt_typ))
        }
    }

    fn infer_param(&mut self, lam: &mut Lambda<'src>, expected_typ: &Type<'src>) {
        match lam.param {
            Some(ref mut param) => match param.typ.infer_by(expected_typ) {
                Some(inferred) => param.typ = inferred,
                None => param.ident.pos.error_exit(TypeMis(expected_typ, &param.typ)),
            },
            None => if expected_typ.infer_by(&TYPE_NIL).is_none() {
                lam.pos.error_exit(NonNilNullary(expected_typ))
            },
        }
    }

    fn infer_lambda<'l>(&mut self,
                        mut lam: &'l mut Lambda<'src>,
                        expected_type: &Type<'src>)
                        -> &'l Type<'src> {
        let (expected_param, expected_body) = expected_type.get_func_sig()
                                                           .unwrap_or((&TYPE_UNINFERRED,
                                                                       &TYPE_UNINFERRED));

        // Own type is `Uninferred` if no type has been inferred yet, or none was inferrable

        if lam.typ.is_partially_known() {
            if let Some(extended_expected_type) = lam.typ.infer_by(expected_type) {
                if lam.typ == extended_expected_type {
                    // Own type can't be inferred further by `expected_type`
                    return &lam.typ;
                }
            } else {
                // Own type and expected type are not compatible. Type mismatch
                lam.pos.error_exit(TypeMis(expected_type, &lam.typ));
            }
        }

        self.infer_param(&mut lam, &expected_param);

        if let Some(ref mut param) = lam.param {
            self.vars.push((param.ident.s, param.typ.clone()));
            self.infer_expr(&mut lam.body, &expected_body);
            param.typ = self.vars
                            .pop()
                            .expect("ICE: Variable stack empty after infer expr when infer lambda")
                            .1;
        } else {
            self.infer_expr(&mut lam.body, &expected_body);
        }

        lam.typ = Type::new_func(get_param_type(&lam.param).clone(),
                                 lam.body.get_type().clone());
        &lam.typ
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

    fn infer_cons(&mut self, cons: &mut Cons<'src>, expected_ty: &Type<'src>) -> Type<'src> {
        let unknown_cons_typ = Type::new_cons(Type::Uninferred, Type::Uninferred);

        let maybe_expected_inferred = expected_ty.infer_by(&unknown_cons_typ);
        if let Some((e_car, e_cdr)) = maybe_expected_inferred.as_ref().and_then(|t| t.get_cons()) {
            let car_typ = self.infer_expr(&mut cons.car, e_car);
            let cdr_typ = self.infer_expr(&mut cons.cdr, e_cdr);
            cons.typ = Type::new_cons(car_typ, cdr_typ);
            cons.typ.clone()
        } else {
            cons.pos.error_exit(TypeMis(expected_ty, &unknown_cons_typ))
        }
    }

    // The type of an expression will only be inferred once
    fn infer_expr(&mut self, expr: &mut Expr<'src>, expected_type: &Type<'src>) -> Type<'src> {
        match *expr {
            Expr::Nil(ref mut nil) => self.infer_nil(nil, expected_type),
            Expr::NumLit(ref mut l) => self.infer_num_lit(l, expected_type),
            Expr::StrLit(ref mut l) => self.infer_str_lit(l, expected_type),
            Expr::Bool(ref mut b) => self.infer_bool(b, expected_type),
            Expr::Binding(ref mut bnd) => self.infer_binding(bnd, expected_type),
            Expr::Call(ref mut call) => self.infer_call(call, expected_type).clone(),
            Expr::If(ref mut cond) => self.infer_if(cond, expected_type),
            Expr::Lambda(ref mut lam) => self.infer_lambda(lam, expected_type).clone(),
            Expr::TypeAscript(_) => self.infer_type_ascript(expr, expected_type),
            Expr::Cons(ref mut cons) => self.infer_cons(cons, expected_type),
        }
    }
}

pub fn infer_types(ast: &mut Module) {
    let mut inferer = Inferer::new(ast);

    let mut main = replace(inferer.static_defs
                                  .get_mut("main")
                                  .expect("ICE: In infer_types: No main def"),
                           None)
                       .unwrap();

    inferer.infer_static_def(&mut main,
                             &Type::new_func(TYPE_NIL.clone(), Type::Const("Int64")));

    inferer.static_defs.update("main", Some(main));

    let (static_defs, extern_funcs) = inferer.into_inner();

    ast.static_defs = static_defs;
    ast.extern_funcs = extern_funcs;
}
