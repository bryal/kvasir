//! Type check and inference

// TODO: Almost all `infer_types` takes const map + var stack + caller stack.
//       Maybe encapsulate this using some kind of state
// TODO: Replace verbose type error checks with:
//       `foo.infer_types(...)
//           .unwrap_or_else(foo.pos().type_mismatcher(expected_ty))`
// TODO: Encode whether types have been inferred in the type of the
//       AST. E.g. `type InferredAst = Ast<Ty = Type>; type UninferredAst = Ast<Ty = Option<Type>>`

// NOTE: If of same let, mutual recursion is possible. Track `let` ID for variable names.
// NOTE: In `if` forms: infer first branch to gather type info,
//       infer second branch to gather more type info, infer first branch again,
//       as new info might have been gathered in second branch

use self::InferenceErr::*;
use lib::front::*;
use lib::front::ast::*;
use lib::front::monomorphization::*;
use lib::front::substitution::*;
use std::collections::{HashMap, BTreeMap, HashSet};
use std::fmt::{self, Display};
use std::iter::{once, FromIterator};
use itertools::{zip, Itertools};

enum InferenceErr<'src> {
    /// Type mismatch. (expected, found)
    TypeMis(Type<'src>, Type<'src>),
    /// Type mismatch with specified mismatching nodes
    TypeMisSub {
        expected: Type<'src>,
        found: Type<'src>,
        sub_expected: Type<'src>,
        sub_found: Type<'src>,
    },
    ArmsDiffer(Type<'src>, Type<'src>),
}

impl<'src> Display for InferenceErr<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeMis(ref expected, ref found) => {
                write!(
                    f,
                    "Type mismatch. Expected `{}`, found `{}`",
                    expected,
                    found
                )
            }
            TypeMisSub {
                ref expected,
                ref found,
                ref sub_expected,
                ref sub_found,
            } => {
                write!(
                    f,
                    "Type mismatch: Expected `{}`, found `{}`\n\
                        Cannot infer or coerce `{}` to `{}`",
                    expected,
                    found,
                    sub_found,
                    sub_expected
                )
            }
            ArmsDiffer(ref c, ref a) => {
                write!(
                    f,
                    "Consequent and alternative have different types. Expected `{}` from \
                        alternative, found `{}`",
                    c,
                    a
                )
            }
        }
    }
}

fn type_mis<'src>(
    type_var_map: &mut HashMap<u64, Type<'src>>,
    expected: &Type<'src>,
    found: &Type<'src>,
) -> InferenceErr<'src> {
    TypeMis(subst(expected, type_var_map), subst(found, type_var_map))
}

fn type_mis_sub<'src>(
    type_var_map: &mut HashMap<u64, Type<'src>>,
    expected: &Type<'src>,
    found: &Type<'src>,
    sub_expected: &Type<'src>,
    sub_found: &Type<'src>,
) -> InferenceErr<'src> {
    TypeMisSub {
        expected: subst(expected, type_var_map),
        found: subst(found, type_var_map),
        sub_expected: subst(sub_expected, type_var_map),
        sub_found: subst(sub_found, type_var_map),
    }
}


/// Returns whether type variable `t` occurs in type `u` with substitutions `s`
///
/// Useful to check for circular type variable mappings
fn occurs_in(t: u64, u: &Type, s: &HashMap<u64, Type>) -> bool {
    match *u {
        Type::Var(ref tv) if t == tv.id => true,
        Type::Var(ref tv) => s.get(&tv.id).map(|u2| occurs_in(t, u2, s)).unwrap_or(false),

        Type::App(_, ref us) => us.iter().any(|u2| occurs_in(t, u2, s)),
        // TODO: Verify that this is correct
        //        Type::Scheme(ref is, ref u2) => !is.contains(&t) && occurs_in(t, u2, s),
        _ => false,
    }
}

// TODO: Method of locking type variables to prevent addition of constraints,
//       for when expected type is provided explicitly by user. E.g. set a LOCKED flag.
//       If a LOCKED type variable needs to be specialized during inference,
//       raise an error instead of adding substitution/constraint/redefinition.

fn wrap_vars_types_in_apps_<'src>(
    e: &mut Expr<'src>,
    vars: &mut HashMap<&'src str, Poly<'src>>,
    app_args: &[Type<'src>],
) {
    let wrap = |p: &Poly<'src>| Type::App(Box::new(TypeFunc::Poly(p.clone())), app_args.to_vec());
    match *e {
        Expr::Variable(ref mut var) => {
            match vars.get(var.ident.s) {
                Some(p) => var.typ = wrap(p),
                None => (),
            }
        }
        Expr::App(ref mut app) => {
            wrap_vars_types_in_apps_(&mut app.func, vars, app_args);
            wrap_vars_types_in_apps_(&mut app.arg, vars, app_args);
        }
        Expr::If(ref mut cond) => {
            wrap_vars_types_in_apps_(&mut cond.predicate, vars, app_args);
            wrap_vars_types_in_apps_(&mut cond.consequent, vars, app_args);
            wrap_vars_types_in_apps_(&mut cond.alternative, vars, app_args);
        }
        Expr::Lambda(ref mut l) => {
            let shadowed = vars.remove(l.param_ident.s);
            wrap_vars_types_in_apps_(&mut l.body, vars, app_args);
            vars.extend(shadowed.into_iter().map(|p| (l.param_ident.s, p)))
        }
        Expr::Let(ref mut l) => {
            let shadoweds = l.bindings
                .ids()
                .filter_map(|id| vars.remove(id).map(|p| (id, p)))
                .collect::<Vec<_>>();
            for binding in l.bindings.bindings_mut() {
                wrap_vars_types_in_apps_(&mut binding.val, vars, app_args);
            }
            wrap_vars_types_in_apps_(&mut l.body, vars, app_args);
            vars.extend(shadoweds)
        }
        Expr::TypeAscript(ref mut a) => wrap_vars_types_in_apps_(&mut a.expr, vars, app_args),
        Expr::Cons(ref mut c) => {
            wrap_vars_types_in_apps_(&mut c.car, vars, app_args);
            wrap_vars_types_in_apps_(&mut c.cdr, vars, app_args);
        }
        Expr::Car(ref mut c) => {
            wrap_vars_types_in_apps_(&mut c.expr, vars, app_args);
        }
        Expr::Cdr(ref mut c) => {
            wrap_vars_types_in_apps_(&mut c.expr, vars, app_args);
        }
        Expr::Cast(ref mut c) => {
            wrap_vars_types_in_apps_(&mut c.expr, vars, app_args);
        }
        Expr::Nil(_) | Expr::NumLit(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}

/// To correctly generate monomorphizations, wrap the type of a recursive
/// variable in an application
fn wrap_vars_types_in_apps<'src>(
    e: &mut Expr<'src>,
    vars: &mut HashMap<&'src str, Poly<'src>>,
    app_args: &[TVar<'src>],
) {
    let app_args_t = app_args.iter().collect::<Vec<_>>();
    wrap_vars_types_in_apps_(
        e,
        vars,
        &app_args_t
            .iter()
            .map(|&tv| Type::Var(tv.clone()))
            .collect::<Vec<_>>(),
    )
}

/// The definition of a type name
enum TypeDef {
    /// It's a core type that can be handled by the code generation backend. E.g. the numeric
    /// types `Int32`, `Float64`, etc.
    Core,
    // TODO: Type alias
    // TODO: Algebraic datatype
}

struct Inferrer<'a, 'src: 'a> {
    /// The environment of variables from let-bindings and function-parameters
    var_env: HashMap<&'src str, Vec<Type<'src>>>,
    /// Declarations of external variables
    externs: &'a BTreeMap<&'src str, ExternDecl<'src>>,
    /// A map of free type variables to their instantiations
    type_var_map: HashMap<u64, Type<'src>>,
    /// Counter for generation of unique type variable ids
    type_var_gen: &'a mut TypeVarGen,
    /// A map of core types and used defined types
    ///
    /// Numeric types, cons, (TODO) type aliases, (TODO) data type definitions
    type_defs: HashMap<&'src str, TypeDef>,
}

impl<'a, 'src: 'a> Inferrer<'a, 'src> {
    fn new(
        externs: &'a BTreeMap<&'src str, ExternDecl<'src>>,
        type_var_gen: &'a mut TypeVarGen,
    ) -> Self {
        use self::TypeDef::*;
        Inferrer {
            var_env: HashMap::new(),
            externs: externs,
            type_var_map: HashMap::new(),
            type_var_gen: type_var_gen,
            type_defs: hashmap! {
                "Int8" => Core,
                "Int16" => Core,
                "Int32" => Core,
                "Int64" => Core,
                "IntPtr" => Core,
                "UInt8" => Core,
                "UInt16" => Core,
                "UInt32" => Core,
                "UInt64" => Core,
                "UIntPtr" => Core,
                "Bool" => Core,
                "Float32" => Core,
                "Float64" => Core,
                "Nil" => Core,
                "RealWorld" => Core,
            },
        }
    }

    fn push_var(&mut self, id: &'src str, t: Type<'src>) {
        self.var_env.entry(id).or_insert(Vec::new()).push(t)
    }

    fn pop_var(&mut self, id: &str) -> Option<Type<'src>> {
        self.var_env.get_mut(id).and_then(|v| v.pop())
    }

    fn get_var(&self, id: &str) -> Option<&Type<'src>> {
        self.var_env.get(id).and_then(|v| v.last())
    }

    /// Returns an iterator of all free type variables that occur in `p`
    fn free_type_vars_poly(&self, p: &Poly<'src>) -> HashSet<TVar<'src>> {
        let mut set = self.free_type_vars(&p.body);
        for tv in &p.params {
            set.remove(&tv);
        }
        set
    }

    /// Returns an iterator of all free type variables that occur in `t`
    fn free_type_vars(&self, t: &Type<'src>) -> HashSet<TVar<'src>> {
        match *t {
            Type::Var(ref tv) => {
                self.type_var_map
                    .get(&tv.id)
                    .map(|u| {
                        if occurs_in(tv.id, u, &self.type_var_map) {
                            // NOTE: Shouldn't be able to happen if no bugs right?
                            panic!("ICE: in get_type_vars: t occurs in u")
                        } else {
                            self.free_type_vars(u)
                        }
                    })
                    .unwrap_or(HashSet::from_iter(once(tv.clone())))
            }
            Type::App(_, ref ts) => {
                ts.iter()
                    .flat_map(move |t2| self.free_type_vars(t2))
                    .collect()
            }
            Type::Poly(ref p) => self.free_type_vars_poly(p),
            _ => HashSet::new(),
        }
    }

    /// Quantifying monotype variables in `t` that are not bound in the context
    ///
    /// Used for generalization.
    fn free_type_vars_in_context(&self, t: &Type<'src>) -> HashSet<TVar<'src>> {
        let env_type_vars = self.var_env
            .iter()
            .flat_map(|(_, v)| v.iter())
            .flat_map(|v_t| self.free_type_vars(v_t))
            .collect::<HashSet<_>>();
        let t_type_vars = self.free_type_vars(t);
        t_type_vars.difference(&env_type_vars).cloned().collect()
    }

    /// Generalize type by quantifying monotype variables in `t` that are not bound in the context
    fn generalize(&self, t: &Type<'src>) -> Type<'src> {
        let frees = self.free_type_vars_in_context(t);
        if frees.is_empty() {
            t.clone()
        } else {
            Type::Poly(Box::new(Poly {
                params: frees.into_iter().collect(),
                body: t.clone(),
            }))
        }
    }

    // TODO: Separate polytypes from normal types?
    /// Instantiate a polymorphic value
    fn instantiate(&mut self, t: &Type<'src>) -> Type<'src> {
        match *t {
            Type::Poly(ref p) => {
                let tvs = p.params
                    .iter()
                    .map(|ref tv| {
                        Type::Var(TVar {
                            id: self.type_var_gen.gen(),
                            constrs: tv.constrs.clone(),
                            explicit: None,
                        })
                    })
                    .collect::<Vec<_>>();
                Type::App(Box::new(TypeFunc::Poly((**p).clone())), tvs)
            }
            _ => t.clone(),
        }
    }

    /// Unify two `Var`s
    fn unify_vars(
        &mut self,
        t: &TVar<'src>,
        u: &TVar<'src>,
    ) -> Result<Type<'src>, (Type<'src>, Type<'src>)> {
        match (t.explicit, t.explicit) {
            (a, b) if a == b => {
                let joined_constrs = Type::Var(TVar {
                    id: self.type_var_gen.gen(),
                    constrs: t.constrs.union(&u.constrs).cloned().collect(),
                    explicit: a.clone(),
                });
                self.type_var_map.insert(t.id, joined_constrs.clone());
                self.type_var_map.insert(u.id, joined_constrs.clone());
                Ok(joined_constrs)
            }
            (Some(_), Some(_)) => Err((Type::Var(t.clone()), Type::Var(u.clone()))),
            (Some(_), None) => {
                self.type_var_map.insert(u.id, Type::Var(t.clone()));
                Ok(Type::Var(t.clone()))
            }
            (None, Some(_)) => self.unify_vars(u, t),
            (None, None) if t.id == u.id => Ok(Type::Var(t.clone())),
            _ => unreachable!(),
        }
    }

    // TODO: Instantiation of circular type. Can it happen?
    /// Unify two types
    ///
    /// Introduce type variables and generate substitutions such that the two types
    /// are equivalent in the resulting environment.
    /// On success, returns the unification. On failure, returns the conflicting nodes
    fn unify<'t>(
        &mut self,
        a: &'t Type<'src>,
        b: &'t Type<'src>,
    ) -> Result<Type<'src>, (Type<'src>, Type<'src>)> {
        use self::Type::*;
        match (a, b) {
            (&Var(ref tv), x) |
            (x, &Var(ref tv)) if self.type_var_map.contains_key(&tv.id) => {
                let t = self.type_var_map[&tv.id].clone();
                self.unify(&t, x)
            }
            (&Var(ref t), &Var(ref u)) => self.unify_vars(t, u),
            (&Var(ref tv), _) if occurs_in(tv.id, b, &self.type_var_map) => {
                panic!("ICE: unify: `{}` occurs in `{}`", tv.id, b);
            }
            (&Var(ref tv), _) if tv.explicit.is_some() => Err((a.clone(), b.clone())),
            (&Var(ref tv), _) if b.fulfills_constraints(&tv.constrs) => {
                self.type_var_map.insert(tv.id, b.clone());
                Ok(b.clone())
            }
            (_, &Var { .. }) => self.unify(b, a),
            (&App(box TypeFunc::Poly(ref p), ref ts), x) |
            (x, &App(box TypeFunc::Poly(ref p), ref ts)) => {
                assert_eq!(p.params.len(), ts.len());
                self.type_var_map.extend(
                    zip(&p.params, ts).map(|(param, t)| {
                        (param.id, t.clone())
                    }),
                );
                let t = subst(&p.body, &mut self.type_var_map);
                for param in &p.params {
                    self.type_var_map.remove(&param.id);
                }
                self.unify(&t, x)
            }
            (&App(box TypeFunc::Const(c1), ref ts1), &App(box TypeFunc::Const(c2), ref ts2))
                if c1 == c2 && ts1.len() == ts2.len() => {
                zip(ts1, ts2)
                    .map(|(t1, t2)| self.unify(t1, t2))
                    .collect::<Result<_, _>>()
                    .map(|us| App(box TypeFunc::Const(c1), us))
            }
            (&Poly(_), _) | (_, &Poly(_)) => {
                println!("unifying polytype: `{}` U `{}`", a, b);
                unimplemented!()
            }
            (&Const(t, ref pos), _) |
            (_, &Const(t, ref pos)) if !self.type_defs.contains_key(t) => {
                pos.as_ref()
                    .expect("ICE: undefined type has no position")
                    .error_exit(format!("Type `{}` not found in this scope", t))
            }
            (_, _) if a == b => Ok(a.clone()),
            _ => Err((a.clone(), b.clone())),
        }
    }

    /// Check that the expected type of a nil expression is unifiable with the nil type
    fn infer_nil(&mut self, nil: &mut Nil<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_NIL).unwrap_or_else(
            |(e, f)| {
                nil.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f))
            },
        )
    }

    /// Check that the expected type of a string literal is unifiable with the string type
    fn infer_str_lit(&mut self, lit: &mut StrLit<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_STRING).unwrap_or_else(
            |(e, f)| {
                lit.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f))
            },
        )
    }

    /// Check that the expected type of a boolean literal is unifiable with the boolean type
    fn infer_bool(&mut self, b: &mut Bool<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_BOOL).unwrap_or_else(
            |(e, f)| {
                b.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f))
            },
        )
    }

    /// Infer the type of a numeric literal
    ///
    /// Type can be one of a selection of numeric types.
    fn infer_num_lit<'n>(
        &mut self,
        lit: &'n mut NumLit<'src>,
        expected_type: &Type<'src>,
    ) -> &'n Type<'src> {
        let mut num_constraint = BTreeSet::new();
        num_constraint.insert("Num");
        let tv_num = Type::Var(TVar {
            id: self.type_var_gen.gen(),
            constrs: num_constraint,
            explicit: None,
        });
        let num_type = self.unify(expected_type, &tv_num).unwrap_or_else(|_| {
            lit.pos.error_exit(format!(
                "Type mismatch. Expected `{}`, found numeric literal",
                expected_type
            ))
        });
        lit.typ = num_type;
        &lit.typ
    }

    /// Infer the type of a variable
    ///
    /// If the variable does not refer to an extern, instantiate the variable
    /// and unify with expected type. If it does refer to an extern,
    /// unify type of extern with expected type.
    fn infer_variable(
        &mut self,
        var: &mut Variable<'src>,
        expected_type: &Type<'src>,
    ) -> Type<'src> {
        if let Some(typ) = self.get_var(var.ident.s).cloned() {
            // Either not an extern, or shadowing an extern. I.e. a lambda parameter or let binding

            // Do not assign unified type to `var.typ`. If definition of var
            // is polymorphic, the application arguments are essential as
            // they may be used in the body of the definition but not show up
            // in the resulting type of the application.
            var.typ = self.instantiate(&typ);
            let unif = self.unify(expected_type, &var.typ).unwrap_or_else(|_| {
                var.ident.pos.error_exit(format!(
                    "Variable of type `{}` cannot be instantiated to expected type `{}`",
                    typ,
                    expected_type
                ))
            });
            unif
        } else if let Some(ext) = self.externs.get(var.ident.s) {
            // An extern. Check that type of extern is unifiable with expected type
            var.typ = self.unify(expected_type, &ext.typ).unwrap_or_else(
                |(e, f)| {
                    var.ident.pos.error_exit(type_mis_sub(
                        &mut self.type_var_map,
                        expected_type,
                        &ext.typ,
                        &e,
                        &f,
                    ))
                },
            );
            var.typ.clone()
        } else {
            var.ident.pos.error_exit(format!(
                "`{}` not found in this scope",
                var.ident.s
            ))
        }
    }

    // TODO: Might introduce type variables that will be bound
    //       in type scheme of binding but does not occur in
    //       actual type of binding? Is this ok?
    //       How to write type ascriptions for such a function?
    //       Alt. force use of PhantomData<T> like inputs?
    /// Infer types in a function application
    fn infer_app<'c>(
        &mut self,
        app: &'c mut App<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let expected_func_type =
            Type::new_func(self.type_var_gen.gen_tv(), self.type_var_gen.gen_tv());
        let func_type = self.infer_expr(&mut app.func, &expected_func_type);
        let expected_arg_type = self.type_var_gen.gen_tv();
        let arg_type = self.infer_expr(&mut app.arg, &expected_arg_type);
        let (func_param_type, func_ret_type) = func_type.get_func().expect(
            "ICE: func_type was not func type in infer_app",
        );
        self.unify(func_param_type, &arg_type).unwrap_or_else(
            |(e, f)| {
                app.arg.pos().error_exit(type_mis_sub(
                    &mut self.type_var_map,
                    func_param_type,
                    &arg_type,
                    &e,
                    &f,
                ))
            },
        );
        let ret_unification = self.unify(expected_type, func_ret_type).unwrap_or_else(
            |(e, f)| {
                app.pos.error_exit(type_mis_sub(
                    &mut self.type_var_map,
                    expected_type,
                    func_ret_type,
                    &e,
                    &f,
                ))
            },
        );
        app.typ = ret_unification;
        &app.typ
    }

    fn infer_if<'i>(
        &mut self,
        cond: &'i mut If<'src>,
        expected_typ: &Type<'src>,
    ) -> &'i Type<'src> {
        self.infer_expr(&mut cond.predicate, &TYPE_BOOL);
        let consequent_type = self.infer_expr(&mut cond.consequent, expected_typ);
        let alternative_type = self.infer_expr(&mut cond.alternative, expected_typ);
        cond.typ = self.unify(&consequent_type, &alternative_type)
            .unwrap_or_else(|_| {
                cond.pos.error_exit(
                    ArmsDiffer(consequent_type, alternative_type),
                )
            });
        &cond.typ
    }

    /// Infer types for a lambda
    fn infer_lambda<'l>(
        &mut self,
        lam: &'l mut Lambda<'src>,
        expected_type: &Type<'src>,
    ) -> &'l Type<'src> {
        // Infer type of param by adding it to the environment and applying constraints based on
        // how it is used during inference of lambda body.

        let param_type = self.type_var_gen.gen_tv();
        let body_type = self.type_var_gen.gen_tv();
        let func_type = Type::new_func(param_type.clone(), body_type);
        let (expected_param_type, expected_body_type) = self.unify(expected_type, &func_type)
            .unwrap_or_else(|_| {
                lam.pos.error_exit(type_mis(
                    &mut self.type_var_map,
                    expected_type,
                    &func_type,
                ))
            })
            .get_func()
            .map(|(p, b)| (p.clone(), b.clone()))
            .expect(
                "ICE: unification with function type did not produce function type in infer_lambda",
            );
        self.push_var(lam.param_ident.s, expected_param_type);

        let body_type = self.infer_expr(&mut lam.body, &expected_body_type);

        lam.param_type = self.pop_var(lam.param_ident.s).expect(
            "ICE: param gone from env in infer_lambda",
        );
        lam.typ = Type::new_func(lam.param_type.clone(), body_type.clone());
        &lam.typ
    }

    fn infer_recursive_binding(&mut self, binding: &mut Binding<'src>, bindings_ids: &[&'src str]) {
        let id = binding.ident.s;
        // Only allow recursion for functions. Stuff like `let a = a + 1`
        // can't be compiled without laziness.
        if binding.val.first_non_type_ascr_is_lambda() {
            self.infer_expr(&mut binding.val, &binding.typ);
        } else {
            let refs_s = if bindings_ids.len() == 1 {
                "itself".to_string()
            } else {
                let siblings_s = bindings_ids
                    .iter()
                    .filter(|s_id| **s_id != id)
                    .map(|s_id| format!("`{}`", s_id))
                    .intersperse(", ".to_string())
                    .collect::<String>();
                format!("itself through sibling bindings {{ {} }}", siblings_s)
            };
            binding.pos.error_exit(format!(
                "Non-function value `{}` defined in terms of {}",
                id,
                refs_s
            ))
        }
    }

    /// Infer types for a group of mutually recursively defined bindings
    fn infer_recursion_group(&mut self, group: &mut Group<'src>) {
        match *group {
            Group::Uncircular(id, ref mut binding) => {
                self.infer_expr(&mut binding.val, &binding.typ);
                binding.typ = self.generalize(&binding.typ);
                self.push_var(id, binding.typ.clone());
            }
            Group::Circular(ref mut bindings) => {
                let bindings_ids = bindings.keys().cloned().collect::<Vec<_>>();
                // Add bindings being inferred to env to allow recursive refs.
                for (id, binding) in bindings.iter() {
                    self.push_var(*id, binding.typ.clone());
                }
                // Infer bindings
                for (_, binding) in bindings.iter_mut() {
                    self.infer_recursive_binding(binding, &bindings_ids)
                }
                // Remove bindings from env to get only surrounding env for generalization
                for (id, _) in bindings.iter() {
                    self.pop_var(id).unwrap_or_else(|| {
                        panic!("ICE: infer_recursion_group: binding gone from var_env")
                    });
                }
                // Because of mutual recursion, all bindings in group must have the
                // same polytype arguments
                let frees = bindings
                    .values()
                    .flat_map(|b| self.free_type_vars_in_context(&b.typ))
                    .unique()
                    .collect::<Vec<_>>();
                if !frees.is_empty() {
                    let mut vars_polys = HashMap::new();
                    for (id, binding) in bindings.iter_mut() {
                        let p = Poly {
                            params: frees.clone(),
                            body: binding.typ.clone(),
                        };
                        binding.typ = Type::Poly(Box::new(p.clone()));
                        vars_polys.insert(*id, p);
                    }
                    for (_, binding) in bindings.iter_mut() {
                        wrap_vars_types_in_apps(&mut binding.val, &mut vars_polys, &frees)
                    }
                }
                // Push vars to env again to make available for the
                // next group in the topological order
                for (id, binding) in bindings.iter() {
                    self.push_var(*id, binding.typ.clone())
                }
            }
        }
    }

    /// Infer types for global bindings or bindings of a let-form
    /// and push them to the environment.
    fn infer_bindings(&mut self, bindings: &mut TopologicallyOrderedDependencyGroups<'src>) {
        for mut recursion_group in bindings.groups_mut().rev() {
            self.infer_recursion_group(recursion_group);
        }
    }

    fn infer_let<'l>(
        &mut self,
        let_: &'l mut Let<'src>,
        expected_type: &Type<'src>,
    ) -> &'l Type<'src> {
        self.infer_bindings(&mut let_.bindings);
        let_.typ = self.infer_expr(&mut let_.body, expected_type).clone();
        for name in let_.bindings.ids() {
            self.pop_var(name).unwrap_or_else(|| {
                panic!("ICE: binding gone from var_env in infer_let")
            });
        }
        &let_.typ
    }

    /// Apply a type ascription and infer type of inner expression
    ///
    /// Unify ascription type with expected type, replace the ascription
    /// with the inner expression it ascribes a type to in the AST,
    /// and infer types for the inner expression
    fn infer_type_ascription(
        &mut self,
        expr: &mut Expr<'src>,
        expected_type: &Type<'src>,
    ) -> Type<'src> {
        let ascr_pos = expr.pos().clone();
        match expr.remove_type_ascription() {
            Some(ascribed) => {
                let expected_type2 = self.unify(expected_type, &ascribed).unwrap_or_else(|_| {
                    ascr_pos.error_exit(type_mis(&mut self.type_var_map, expected_type, &ascribed))
                });
                self.infer_expr(expr, &expected_type2)
            }
            None => panic!("ICE: infer_type_ascript called for non-ascription expr"),
        }
    }

    fn infer_cons<'c>(
        &mut self,
        cons: &'c mut Cons<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let arbitrary_cons_type =
            Type::new_cons(self.type_var_gen.gen_tv(), self.type_var_gen.gen_tv());
        let expected_type2 = self.unify(expected_type, &arbitrary_cons_type)
            .unwrap_or_else(|_| {
                cons.pos.error_exit(type_mis(
                    &mut self.type_var_map,
                    expected_type,
                    &arbitrary_cons_type,
                ))
            });
        let (expected_car_type, expected_cdr_type) = expected_type2.get_cons().expect(
            "ICE: expected type not cons in infer_cons ",
        );
        let car_type = self.infer_expr(&mut cons.car, expected_car_type);
        let cdr_type = self.infer_expr(&mut cons.cdr, expected_cdr_type);
        cons.typ = Type::new_cons(car_type, cdr_type);
        &cons.typ
    }

    fn infer_car<'c>(
        &mut self,
        car: &'c mut Car<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let expected_cons_type = Type::new_cons(expected_type.clone(), self.type_var_gen.gen_tv());
        let cons_type = self.infer_expr(&mut car.expr, &expected_cons_type);
        car.typ = cons_type
            .get_cons()
            .expect("ICE: inner type type not cons in infer_car")
            .0
            .clone();
        &car.typ
    }

    fn infer_cdr<'c>(
        &mut self,
        cdr: &'c mut Cdr<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let expected_cons_type = Type::new_cons(self.type_var_gen.gen_tv(), expected_type.clone());
        let cons_type = self.infer_expr(&mut cdr.expr, &expected_cons_type);
        cdr.typ = cons_type
            .get_cons()
            .expect("ICE: inner type type not cons in infer_cdr")
            .1
            .clone();
        &cdr.typ
    }

    fn infer_cast<'c>(
        &mut self,
        cast: &'c mut Cast<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let expected_from = self.type_var_gen.gen_tv();
        self.infer_expr(&mut cast.expr, &expected_from);
        cast.typ = self.unify(expected_type, &cast.typ).unwrap_or_else(|_| {
            cast.pos.error_exit(type_mis(
                &mut self.type_var_map,
                expected_type,
                &cast.typ,
            ))
        });
        &cast.typ
    }

    // The type of an expression will only be inferred once
    fn infer_expr(&mut self, expr: &mut Expr<'src>, expected_type: &Type<'src>) -> Type<'src> {
        match *expr {
            Expr::Nil(ref mut nil) => self.infer_nil(nil, expected_type),
            Expr::StrLit(ref mut l) => self.infer_str_lit(l, expected_type),
            Expr::Bool(ref mut b) => self.infer_bool(b, expected_type),
            Expr::NumLit(ref mut l) => self.infer_num_lit(l, expected_type).clone(),
            Expr::Variable(ref mut var) => self.infer_variable(var, expected_type).clone(),
            Expr::App(ref mut app) => self.infer_app(app, expected_type).clone(),
            Expr::If(ref mut cond) => self.infer_if(cond, expected_type).clone(),
            Expr::Lambda(ref mut lam) => self.infer_lambda(lam, expected_type).clone(),
            Expr::Let(ref mut l) => self.infer_let(l, expected_type).clone(),
            Expr::TypeAscript(_) => self.infer_type_ascription(expr, expected_type),
            Expr::Cons(ref mut cons) => self.infer_cons(cons, expected_type).clone(),
            Expr::Car(ref mut c) => self.infer_car(c, expected_type).clone(),
            Expr::Cdr(ref mut c) => self.infer_cdr(c, expected_type).clone(),
            Expr::Cast(ref mut c) => self.infer_cast(c, expected_type).clone(),            
        }
    }
}

fn assert_externs_monomorphic(externs: &BTreeMap<&str, ExternDecl>) {
    for ext in externs.values() {
        if !ext.typ.is_monomorphic() {
            ext.pos.error_exit(
                "Type of external declaration must be monomorphic",
            )
        }
    }
}

pub fn infer_types(ast: &mut Ast, type_var_generator: &mut TypeVarGen) {
    assert_externs_monomorphic(&ast.externs);
    let mut inferrer = Inferrer::new(&mut ast.externs, type_var_generator);
    inferrer.infer_bindings(&mut ast.globals);

    // Apply all substitutions recursively to get rid of reduntant, indirect type variables
    for binding in ast.globals.bindings_mut() {
        binding.typ = subst(&binding.typ, &mut inferrer.type_var_map);
        subst_expr(&mut binding.val, &mut inferrer.type_var_map);
    }

    // Map monomorphic instantiations of variables to monomorphization of definitions
    monomorphize_defs_of_insts(&mut ast.globals);
}
