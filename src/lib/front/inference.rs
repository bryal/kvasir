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
use lib::set_of;
use lib::front::*;
use lib::front::ast::*;
use lib::front::monomorphization::*;
use lib::front::substitution::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};
use itertools::{zip, Itertools};

lazy_static! {
    pub static ref EMPTY_SET: BTreeSet<&'static str> = BTreeSet::new();
}

enum InferenceErr<'s> {
    /// Type mismatch. (expected, found)
    TypeMis(Type<'s>, Type<'s>),
    /// Type mismatch with specified mismatching nodes
    TypeMisSub {
        expected: Type<'s>,
        found: Type<'s>,
        sub_expected: Type<'s>,
        sub_found: Type<'s>,
    },
    ArmsDiffer(Type<'s>, Type<'s>),
    ConstrWrongNumArgs {
        expected: usize,
        found: usize,
    },
}

impl<'s> Display for InferenceErr<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeMis(ref expected, ref found) => write!(
                f,
                "Type mismatch. Expected `{}`, found `{}`",
                expected, found
            ),
            TypeMisSub {
                ref expected,
                ref found,
                ref sub_expected,
                ref sub_found,
            } => write!(
                f,
                "Type mismatch: Expected `{}`, found `{}`\n\
                 Cannot infer or coerce `{}` to `{}`",
                expected, found, sub_found, sub_expected
            ),
            ArmsDiffer(ref c, ref a) => write!(
                f,
                "Consequent and alternative have different types. Expected `{}` from \
                 alternative, found `{}`",
                c, a
            ),
            ConstrWrongNumArgs { expected, found } => write!(
                f,
                "Wrong number of arguments in constructor in pattern. Expected {}, found {}",
                expected, found
            ),
        }
    }
}

fn type_mis<'s>(
    type_var_map: &mut BTreeMap<TVar<'s>, Type<'s>>,
    expected: &Type<'s>,
    found: &Type<'s>,
) -> InferenceErr<'s> {
    TypeMis(subst(expected, type_var_map), subst(found, type_var_map))
}

fn type_mis_sub<'s>(
    type_var_map: &mut BTreeMap<TVar<'s>, Type<'s>>,
    expected: &Type<'s>,
    found: &Type<'s>,
    sub_expected: &Type<'s>,
    sub_found: &Type<'s>,
) -> InferenceErr<'s> {
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
fn occurs_in(t: &TVar, u: &Type, s: &BTreeMap<TVar, Type>) -> bool {
    match *u {
        Type::Var(ref tv) if t == tv => true,
        Type::Var(ref tv) => s.get(&tv).map(|u2| occurs_in(t, u2, s)).unwrap_or(false),
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

fn wrap_vars_types_in_apps_match<'s>(
    m: &mut Match<'s>,
    vars: &mut BTreeMap<&'s str, Poly<'s>>,
    app_args: &[Type<'s>],
) {
    for case in &mut m.cases {
        let shadoweds = case.patt
            .variable_names()
            .into_iter()
            .filter_map(|id| vars.remove(id).map(|p| (id, p)))
            .collect::<Vec<_>>();
        wrap_vars_types_in_apps_(&mut case.body, vars, app_args);
        vars.extend(shadoweds)
    }
}

fn wrap_vars_types_in_apps_<'s>(
    e: &mut Expr<'s>,
    vars: &mut BTreeMap<&'s str, Poly<'s>>,
    app_args: &[Type<'s>],
) {
    let wrap = |p: &Poly<'s>| Type::App(Box::new(TypeFunc::Poly(p.clone())), app_args.to_vec());
    match *e {
        Expr::Variable(ref mut var) => match vars.get(var.ident.s) {
            Some(p) => var.typ = wrap(p),
            None => (),
        },
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
        Expr::New(ref mut n) => for member in &mut n.members {
            wrap_vars_types_in_apps_(member, vars, app_args)
        },
        Expr::Match(ref mut m) => wrap_vars_types_in_apps_match(m, vars, app_args),
        Expr::Nil(_) | Expr::NumLit(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}

/// To correctly generate monomorphizations, wrap the type of a recursive
/// variable in an application
fn wrap_vars_types_in_apps<'s>(
    e: &mut Expr<'s>,
    vars: &mut BTreeMap<&'s str, Poly<'s>>,
    app_args: &[TVar<'s>],
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
    /// An algebraic data type with variants and members
    Adt,
    // TODO: Type alias
}

struct Inferrer<'a, 's: 'a> {
    /// The environment of variables from let-bindings and function-parameters
    var_env: BTreeMap<&'s str, Vec<Type<'s>>>,
    /// Declarations of external variables
    externs: &'a BTreeMap<&'s str, ExternDecl<'s>>,
    /// Environment of what constraints are bound to a type variable
    type_var_env: BTreeMap<TVar<'s>, BTreeSet<&'s str>>,
    type_var_map: BTreeMap<TVar<'s>, Type<'s>>,
    /// Counter for generation of unique type variable ids
    type_var_gen: &'a mut TypeVarGen,
    /// Defined algebraic data types
    adts: &'a Adts<'s>,
    /// A map of core types and used defined types
    ///
    /// Numeric types, cons, (TODO) type aliases, data type definitions
    type_defs: BTreeMap<&'s str, TypeDef>,
}

impl<'a, 's: 'a> Inferrer<'a, 's> {
    fn new(
        externs: &'a BTreeMap<&'s str, ExternDecl<'s>>,
        adts: &'a Adts<'s>,
        type_var_gen: &'a mut TypeVarGen,
    ) -> Self {
        use self::TypeDef::*;
        let mut type_defs = btreemap! {
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
        };
        type_defs.extend(adts.defs.iter().map(|(&k, _)| (k, TypeDef::Adt)));
        Inferrer {
            var_env: BTreeMap::new(),
            externs,
            type_var_env: BTreeMap::new(),
            type_var_map: BTreeMap::new(),
            type_var_gen,
            adts,
            type_defs,
        }
    }

    // pub fn get_type(&self) -> Type<'s> {
    //     Type::new_tuple(&self.members)
    // }

    pub fn get_type_of_adt(&mut self, name: &str) -> Option<Type<'s>> {
        self.adts.defs.get(name).map(|adt| {
            if adt.params.is_empty() {
                Type::Const(adt.name.s, None)
            } else {
                Type::App(
                    box TypeFunc::Const(adt.name.s),
                    adt.params
                        .iter()
                        .map(|_| self.type_var_gen.gen_type_var())
                        .collect(),
                )
            }
        })
    }

    pub fn parent_type_of_variant(&mut self, v: &str) -> Option<Type<'s>> {
        self.adts
            .variants
            .get(v)
            .and_then(|s| self.get_type_of_adt(s))
    }

    // pub fn type_of_variant(&self, v: &str) -> Option<Type<'s>> {
    //     self.adt_variant_of_name(v).map(AdtVariant::get_type)
    // }

    // pub fn constructor_type_of_variant(&self, v: &str) -> Option<Type<'s>> {
    //     let adt_variant = self.adt_variant_of_name(v)?;
    //     let parent_type = self.parent_type_of_variant(v)?;
    //     Some(Type::new_currying_func(&adt_variant.members, parent_type))
    // }

    fn push_var(&mut self, id: &'s str, t: Type<'s>) {
        self.var_env.entry(id).or_insert(Vec::new()).push(t)
    }

    fn pop_var(&mut self, id: &str) -> Option<Type<'s>> {
        self.var_env.get_mut(id).and_then(|v| v.pop())
    }

    fn get_var(&self, id: &str) -> Option<&Type<'s>> {
        self.var_env.get(id).and_then(|v| v.last())
    }

    fn extend_type_var_env(&mut self, tvs: BTreeMap<TVar<'s>, BTreeSet<&'s str>>) {
        for (tv, constrs) in tvs {
            self.type_var_env.insert(tv, constrs);
        }
    }

    fn extend_type_var_env_no_constrs(&mut self, tvs: &BTreeSet<TVar<'s>>) {
        for &tv in tvs {
            self.type_var_env.entry(tv).or_insert(BTreeSet::new());
        }
    }

    fn unextend_type_var_env<I>(&mut self, tvs: I)
    where
        I: IntoIterator<Item = TVar<'s>>,
    {
        for tv in tvs {
            self.type_var_env.remove(&tv);
        }
    }

    fn get_type_var_constraints(&self, id: &TVar<'s>) -> &BTreeSet<&'s str> {
        self.type_var_env.get(id).unwrap_or(&EMPTY_SET)
    }

    /// Returns an iterator of all free type variables that occur in `p`
    fn free_type_vars_poly(&self, p: &Poly<'s>) -> BTreeSet<TVar<'s>> {
        let mut set = self.free_type_vars(&p.body);
        for (param_v, _) in &p.params {
            set.remove(param_v);
        }
        set
    }

    fn free_type_vars_var(&self, tv: &TVar<'s>) -> BTreeSet<TVar<'s>> {
        self.type_var_map
            .get(tv)
            .map(|u| {
                if occurs_in(tv, u, &self.type_var_map) {
                    // NOTE: Shouldn't be able to happen if no bugs right?
                    panic!("ICE: in get_type_vars: t occurs in u")
                } else {
                    self.free_type_vars(u)
                }
            })
            .unwrap_or(set_of(tv.clone()))
    }

    /// Returns an iterator of all free type variables that occur in `t`
    fn free_type_vars(&self, t: &Type<'s>) -> BTreeSet<TVar<'s>> {
        match *t {
            Type::Var(ref tv) => self.free_type_vars_var(tv),
            Type::App(_, ref ts) => ts.iter()
                .flat_map(move |t2| self.free_type_vars(t2))
                .collect(),
            Type::Poly(ref p) => self.free_type_vars_poly(p),
            Type::Const(..) => BTreeSet::new(),
        }
    }

    fn bound_type_vars_in_env(
        &self,
        env: &BTreeMap<TVar<'s>, BTreeSet<&'s str>>,
    ) -> BTreeSet<TVar<'s>> {
        env.keys()
            .flat_map(|tv| self.free_type_vars_var(tv))
            .collect()
    }

    /// Quantifying monotype variables in `t` that are not bound in the context
    ///
    /// Used for generalization.
    fn free_type_vars_in_context(
        &self,
        t: &Type<'s>,
        context: &BTreeMap<TVar<'s>, BTreeSet<&'s str>>,
    ) -> BTreeSet<TVar<'s>> {
        &self.free_type_vars(t) - &self.bound_type_vars_in_env(context)
        // for tv in context.keys() {
        //     tvs.remove(tv);
        // }
        // tvs
    }

    /// Generalize type by quantifying monotype variables in `t` that are not bound in the context
    fn generalize(
        &self,
        t: &Type<'s>,
        context: &BTreeMap<TVar<'s>, BTreeSet<&'s str>>,
    ) -> BTreeMap<TVar<'s>, BTreeSet<&'s str>> {
        self.free_type_vars_in_context(t, context)
            .into_iter()
            .map(|tv| (tv, self.get_type_var_constraints(&tv).clone()))
            .collect()
    }

    /// Instantiate a polymorphic value
    fn instantiate(&mut self, t: &Type<'s>) -> Type<'s> {
        match *t {
            Type::Poly(ref p) => {
                let fresh_tvs = p.params
                    .iter()
                    .map(|(_, constrs)| {
                        let tv = self.type_var_gen.gen_tv();
                        self.type_var_env.insert(tv, constrs.clone());
                        Type::Var(tv)
                    })
                    .collect::<Vec<_>>();
                Type::App(Box::new(TypeFunc::Poly((**p).clone())), fresh_tvs)
            }
            _ => t.clone(),
        }
    }

    fn unify_vars(&mut self, t: &TVar<'s>, u: &TVar<'s>) -> Result<TVar<'s>, (Type<'s>, Type<'s>)> {
        use self::TVar::*;
        match (*t, *u) {
            (Explicit(a), Explicit(b)) => if a == b {
                Ok(t.clone())
            } else {
                Err((Type::Var(t.clone()), Type::Var(u.clone())))
            },
            (Implicit(_), Explicit(_)) => {
                let is_subset = {
                    let t_constrs = self.get_type_var_constraints(t);
                    let u_constrs = self.get_type_var_constraints(u);
                    t_constrs.is_subset(&u_constrs)
                };
                let v = u.clone();
                if is_subset {
                    self.type_var_map.insert(*t, Type::Var(v));
                    Ok(v)
                } else {
                    Err((Type::Var(t.clone()), Type::Var(v)))
                }
            }
            (Explicit(_), Implicit(_)) => self.unify_vars(u, t),
            (Implicit(a), Implicit(b)) => {
                let joined_constrs = {
                    let t_constrs = self.get_type_var_constraints(t);
                    let u_constrs = self.get_type_var_constraints(u);
                    t_constrs | u_constrs
                };
                let joined_constrs_tv = self.type_var_gen.gen_tv();
                self.type_var_env.insert(joined_constrs_tv, joined_constrs);
                self.type_var_map.insert(*t, Type::Var(joined_constrs_tv));
                if a != b {
                    self.type_var_map.insert(*u, Type::Var(joined_constrs_tv));
                }
                Ok(joined_constrs_tv)
            }
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
        a: &'t Type<'s>,
        b: &'t Type<'s>,
    ) -> Result<Type<'s>, (Type<'s>, Type<'s>)> {
        use self::Type::*;
        match (a, b) {
            (&Var(ref tv), x) | (x, &Var(ref tv)) if self.type_var_map.contains_key(tv) => {
                let t = self.type_var_map[tv].clone();
                self.unify(&t, x)
            }
            (&App(box TypeFunc::Poly(ref p), ref ts), x)
            | (x, &App(box TypeFunc::Poly(ref p), ref ts)) => {
                assert_eq!(p.params.len(), ts.len());
                self.type_var_map.extend(
                    p.params
                        .iter()
                        .zip(ts)
                        .map(|((&param_v, _), t)| (param_v, t.clone())),
                );
                let t = subst(&p.body, &mut self.type_var_map);
                for (tv, _) in &p.params {
                    self.type_var_map.remove(tv);
                }
                self.unify(&t, x)
            }
            (&Var(ref t), &Var(ref u)) => self.unify_vars(t, u).map(Type::Var),
            (&Var(ref tv), _) if occurs_in(tv, b, &self.type_var_map) => {
                panic!("ICE: unify: `{}` occurs in `{}`", tv, b);
            }
            (&Var(TVar::Explicit(_)), _) => Err((a.clone(), b.clone())),
            (&Var(ref tv), _) => {
                let fulfills_constrs = {
                    let tv_constrs = self.get_type_var_constraints(tv);
                    b.fulfills_constraints(&tv_constrs)
                };
                if fulfills_constrs {
                    self.type_var_map.insert(*tv, b.clone());
                    Ok(b.clone())
                } else {
                    Err((a.clone(), b.clone()))
                }
            }
            (_, &Var(_)) => self.unify(b, a),
            (&App(box TypeFunc::Const(c1), ref ts1), &App(box TypeFunc::Const(c2), ref ts2))
                if c1 == c2 && ts1.len() == ts2.len() =>
            {
                zip(ts1, ts2)
                    .map(|(t1, t2)| self.unify(t1, t2))
                    .collect::<Result<_, _>>()
                    .map(|us| App(box TypeFunc::Const(c1), us))
            }
            (&Poly(_), _) | (_, &Poly(_)) => {
                println!("unifying polytype: `{}` U `{}`", a, b);
                unimplemented!()
            }
            (&Const(t, ref pos), _) | (_, &Const(t, ref pos))
                if !self.type_defs.contains_key(t) =>
            {
                pos.as_ref()
                    .expect("ICE: undefined type has no position")
                    .error_exit(format!("Type `{}` not found in this scope", t))
            }
            (_, _) if a == b => Ok(a.clone()),
            _ => Err((a.clone(), b.clone())),
        }
    }

    /// Check that the expected type of a nil expression is unifiable with the nil type
    fn infer_nil(&mut self, nil: &mut Nil<'s>, expected_type: &Type<'s>) -> Type<'s> {
        self.unify(expected_type, &TYPE_NIL)
            .unwrap_or_else(|(e, f)| nil.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f)))
    }

    /// Check that the expected type of a string literal is unifiable with the string type
    fn infer_str_lit(&mut self, lit: &mut StrLit<'s>, expected_type: &Type<'s>) -> Type<'s> {
        self.unify(expected_type, &TYPE_STRING)
            .unwrap_or_else(|(e, f)| lit.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f)))
    }

    /// Check that the expected type of a boolean literal is unifiable with the boolean type
    fn infer_bool(&mut self, b: &mut Bool<'s>, expected_type: &Type<'s>) -> Type<'s> {
        self.unify(expected_type, &TYPE_BOOL)
            .unwrap_or_else(|(e, f)| b.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f)))
    }

    /// Infer the type of a numeric literal
    ///
    /// Type can be one of a selection of numeric types.
    fn infer_num_lit<'n>(
        &mut self,
        lit: &'n mut NumLit<'s>,
        expected_type: &Type<'s>,
    ) -> &'n Type<'s> {
        if lit.lit.contains('.') {
            lit.typ = self.unify(expected_type, &TYPE_FLOAT64)
                .unwrap_or_else(|(e, f)| {
                    lit.pos.error_exit(type_mis(&mut self.type_var_map, &e, &f))
                });
            &lit.typ
        } else {
            let num_constraint = set_of("Num");
            let tv_num = self.type_var_gen.gen_tv();
            self.type_var_env.insert(tv_num, num_constraint);
            lit.typ = self.unify(expected_type, &Type::Var(tv_num))
                .unwrap_or_else(|_| {
                    lit.pos.error_exit(format!(
                        "Type mismatch. Expected `{}`, found numeric literal",
                        expected_type
                    ))
                });
            &lit.typ
        }
    }

    /// Infer the type of a variable
    ///
    /// If the variable does not refer to an extern, instantiate the variable
    /// and unify with expected type. If it does refer to an extern,
    /// unify type of extern with expected type.
    fn infer_variable(&mut self, var: &mut Variable<'s>, expected_type: &Type<'s>) -> Type<'s> {
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
                    typ, expected_type
                ))
            });
            unif
        } else if let Some(ext) = self.externs.get(var.ident.s) {
            // An extern. Check that type of extern is unifiable with expected type
            var.typ = self.unify(expected_type, &ext.typ)
                .unwrap_or_else(|(e, f)| {
                    var.ident.pos.error_exit(type_mis_sub(
                        &mut self.type_var_map,
                        expected_type,
                        &ext.typ,
                        &e,
                        &f,
                    ))
                });
            var.typ.clone()
        } else {
            var.ident
                .pos
                .error_exit(format!("`{}` not found in this scope", var.ident.s))
        }
    }

    // TODO: Might introduce type variables that will be bound
    //       in type scheme of binding but does not occur in
    //       actual type of binding? Is this ok?
    //       How to write type ascriptions for such a function?
    //       Alt. force use of PhantomData<T> like inputs?
    /// Infer types in a function application
    fn infer_app<'c>(&mut self, app: &'c mut App<'s>, expected_type: &Type<'s>) -> &'c Type<'s> {
        let expected_func_type = Type::new_func(
            self.type_var_gen.gen_type_var(),
            self.type_var_gen.gen_type_var(),
        );
        let func_type = self.infer_expr(&mut app.func, &expected_func_type);
        let expected_arg_type = self.type_var_gen.gen_type_var();
        let arg_type = self.infer_expr(&mut app.arg, &expected_arg_type);
        let (func_param_type, func_ret_type) = func_type
            .get_func()
            .expect("ICE: func_type was not func type in infer_app");
        self.unify(func_param_type, &arg_type)
            .unwrap_or_else(|(e, f)| {
                app.arg.pos().error_exit(type_mis_sub(
                    &mut self.type_var_map,
                    func_param_type,
                    &arg_type,
                    &e,
                    &f,
                ))
            });
        let ret_unification = self.unify(expected_type, func_ret_type)
            .unwrap_or_else(|(e, f)| {
                app.pos.error_exit(type_mis_sub(
                    &mut self.type_var_map,
                    expected_type,
                    func_ret_type,
                    &e,
                    &f,
                ))
            });
        app.typ = ret_unification;
        &app.typ
    }

    fn infer_if<'i>(&mut self, cond: &'i mut If<'s>, expected_typ: &Type<'s>) -> &'i Type<'s> {
        self.infer_expr(&mut cond.predicate, &TYPE_BOOL);
        let consequent_type = self.infer_expr(&mut cond.consequent, expected_typ);
        let alternative_type = self.infer_expr(&mut cond.alternative, expected_typ);
        cond.typ = self.unify(&consequent_type, &alternative_type)
            .unwrap_or_else(|_| {
                cond.pos
                    .error_exit(ArmsDiffer(consequent_type, alternative_type))
            });
        &cond.typ
    }

    /// Infer types for a lambda
    fn infer_lambda<'l>(
        &mut self,
        lam: &'l mut Lambda<'s>,
        expected_type: &Type<'s>,
    ) -> &'l Type<'s> {
        // Infer type of param by adding it to the environment and applying constraints based on
        // how it is used during inference of lambda body.

        lam.typ = Type::new_func(
            self.type_var_gen.gen_type_var(),
            self.type_var_gen.gen_type_var(),
        );
        let (expected_param_type, expected_body_type) = self.unify(expected_type, &lam.typ)
            .unwrap_or_else(|_| {
                lam.pos
                    .error_exit(type_mis(&mut self.type_var_map, expected_type, &lam.typ))
            })
            .get_func()
            .map(|(p, b)| (p.clone(), b.clone()))
            .expect(
                "ICE: unification with function type did not produce function type in infer_lambda",
            );
        let param_tvars = self.free_type_vars(&expected_param_type);
        self.extend_type_var_env_no_constrs(&param_tvars);
        self.push_var(lam.param_ident.s, expected_param_type);
        self.infer_expr(&mut lam.body, &expected_body_type);
        self.pop_var(lam.param_ident.s);
        self.unextend_type_var_env(param_tvars);
        &lam.typ
    }

    fn infer_recursive_binding(&mut self, binding: &mut Binding<'s>, bindings_ids: &[&'s str]) {
        let id = binding.ident.s;
        // Only allow recursion for functions. Stuff like `let a = a + 1`
        // can't be compiled without laziness.
        if binding.val.first_non_type_ascr_is_lambda() {
            self.infer_expr(&mut binding.val, &binding.sig.body);
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
                id, refs_s
            ))
        }
    }

    /// Infer types for a group of mutually recursively defined bindings
    fn infer_recursion_group(&mut self, group: &mut Group<'s>) {
        match *group {
            Group::Uncircular(id, ref mut binding) => {
                let old_tv_env = self.type_var_env.clone();
                self.extend_type_var_env(binding.sig.params.clone());
                self.infer_expr(&mut binding.val, &binding.sig.body);
                let generalized_params = self.generalize(&binding.sig.body, &old_tv_env);
                binding.sig.params = generalized_params;
                self.push_var(id, binding.get_type());
                self.type_var_env = old_tv_env;
            }
            Group::Circular(ref mut bindings) => {
                let old_tv_env = self.type_var_env.clone();
                let mut bindings_ids = vec![];
                // Add bindings being inferred to env to allow recursive refs.
                for (&id, binding) in bindings.iter() {
                    self.push_var(id, binding.sig.body.clone());
                    bindings_ids.push(id);
                    self.extend_type_var_env(binding.sig.params.clone());
                }
                // Infer bindings
                for (_, binding) in bindings.iter_mut() {
                    self.infer_recursive_binding(binding, &bindings_ids)
                }
                for (id, _) in bindings.iter() {
                    self.pop_var(id).unwrap_or_else(|| {
                        panic!("ICE: infer_recursion_group: binding gone from var_env")
                    });
                }
                // Because of mutual recursion, all bindings in group must have the
                // same polytype arguments
                let generalized_params = bindings
                    .values()
                    .flat_map(|b| self.generalize(&b.sig.body, &old_tv_env))
                    .collect::<BTreeMap<_, _>>();
                let mut vars_polys = BTreeMap::new();
                for (id, binding) in bindings.iter_mut() {
                    binding.sig.params = generalized_params.clone();
                    vars_polys.insert(*id, binding.sig.clone());
                }
                for (_, binding) in bindings.iter_mut() {
                    wrap_vars_types_in_apps(
                        &mut binding.val,
                        &mut vars_polys,
                        &generalized_params.keys().cloned().collect::<Vec<_>>(),
                    )
                }
                // Push vars to env again to make available for the
                // next group in the topological order
                for (id, binding) in bindings.iter() {
                    self.push_var(*id, Type::Poly(box binding.sig.clone()))
                }
                self.type_var_env = old_tv_env;
            }
        }
    }

    /// Infer types for global bindings or bindings of a let-form
    /// and push them to the environment.
    fn infer_bindings(&mut self, bindings: &mut TopologicallyOrderedDependencyGroups<'s>) {
        for mut recursion_group in bindings.groups_mut().rev() {
            self.infer_recursion_group(recursion_group);
        }
    }

    fn infer_let<'l>(&mut self, let_: &'l mut Let<'s>, expected_type: &Type<'s>) -> &'l Type<'s> {
        self.infer_bindings(&mut let_.bindings);
        let_.typ = self.infer_expr(&mut let_.body, expected_type).clone();
        for name in let_.bindings.ids() {
            self.pop_var(name)
                .unwrap_or_else(|| panic!("ICE: binding gone from var_env in infer_let"));
        }
        &let_.typ
    }

    /// Apply a type ascription and infer type of inner expression
    ///
    /// Unify ascription type with expected type, replace the ascription
    /// with the inner expression it ascribes a type to in the AST,
    /// and infer types for the inner expression
    fn infer_type_ascription(&mut self, expr: &mut Expr<'s>, expected_type: &Type<'s>) -> Type<'s> {
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

    fn infer_cons<'c>(&mut self, cons: &'c mut Cons<'s>, expected_type: &Type<'s>) -> &'c Type<'s> {
        let arbitrary_cons_type = Type::new_cons(
            self.type_var_gen.gen_type_var(),
            self.type_var_gen.gen_type_var(),
        );
        let expected_type2 = self.unify(expected_type, &arbitrary_cons_type)
            .unwrap_or_else(|_| {
                cons.pos.error_exit(type_mis(
                    &mut self.type_var_map,
                    expected_type,
                    &arbitrary_cons_type,
                ))
            });
        let (expected_car_type, expected_cdr_type) = expected_type2
            .get_cons()
            .expect("ICE: expected type not cons in infer_cons ");
        let car_type = self.infer_expr(&mut cons.car, expected_car_type);
        let cdr_type = self.infer_expr(&mut cons.cdr, expected_cdr_type);
        cons.typ = Type::new_cons(car_type, cdr_type);
        &cons.typ
    }

    fn infer_car<'c>(&mut self, car: &'c mut Car<'s>, expected_type: &Type<'s>) -> &'c Type<'s> {
        let expected_cons_type =
            Type::new_cons(expected_type.clone(), self.type_var_gen.gen_type_var());
        let cons_type = self.infer_expr(&mut car.expr, &expected_cons_type);
        car.typ = cons_type
            .get_cons()
            .expect("ICE: inner type type not cons in infer_car")
            .0
            .clone();
        &car.typ
    }

    fn infer_cdr<'c>(&mut self, cdr: &'c mut Cdr<'s>, expected_type: &Type<'s>) -> &'c Type<'s> {
        let expected_cons_type =
            Type::new_cons(self.type_var_gen.gen_type_var(), expected_type.clone());
        let cons_type = self.infer_expr(&mut cdr.expr, &expected_cons_type);
        cdr.typ = cons_type
            .get_cons()
            .expect("ICE: inner type type not cons in infer_cdr")
            .1
            .clone();
        &cdr.typ
    }

    fn infer_cast<'c>(&mut self, cast: &'c mut Cast<'s>, expected_type: &Type<'s>) -> &'c Type<'s> {
        let expected_from = self.type_var_gen.gen_type_var();
        self.infer_expr(&mut cast.expr, &expected_from);
        cast.typ = self.unify(expected_type, &cast.typ).unwrap_or_else(|_| {
            cast.pos
                .error_exit(type_mis(&mut self.type_var_map, expected_type, &cast.typ))
        });
        &cast.typ
    }

    fn infer_new<'n>(&mut self, n: &'n mut New<'s>, expected_type: &Type<'s>) -> &'n Type<'s> {
        n.typ = self.parent_type_of_variant(n.constr.s)
            .expect("ICE: No type_of_variant in infer_new");
        n.typ = self.unify(expected_type, &n.typ).unwrap_or_else(|_| {
            n.pos
                .error_exit(type_mis(&mut self.type_var_map, expected_type, &n.typ))
        });
        let inst = n.typ.get_adt_inst_args().unwrap_or(&[]);
        let expected_member_types = self.adts
            .members_with_inst_of_variant_with_name(n.constr.s, inst)
            .expect("ICE: No adt_variant_of_name in infer_new");
        for (member, expected_member_type) in n.members.iter_mut().zip(expected_member_types) {
            self.infer_expr(member, &expected_member_type);
        }
        &n.typ
    }

    fn infer_pattern(&mut self, patt: &mut Pattern<'s>, expected_type: &Type<'s>) -> Type<'s> {
        match *patt {
            Pattern::Nil(ref mut nil) => self.infer_nil(nil, expected_type),
            Pattern::NumLit(ref mut num) => self.infer_num_lit(num, expected_type).clone(),
            Pattern::StrLit(ref mut lit) => self.infer_str_lit(lit, expected_type),
            Pattern::Variable(ref mut var) => {
                var.typ = expected_type.clone();
                var.typ.clone()
            }
            Pattern::Deconstr(ref mut dec) => {
                let adt_type = self.parent_type_of_variant(dec.constr.s).expect(&format!(
                    "ICE: No parent type of variant `{}` in infer_pattern",
                    dec.constr.s,
                ));
                let adt_inst = adt_type.get_adt_inst_args().unwrap_or(&[]);
                let typ = self.unify(expected_type, &adt_type).unwrap_or_else(|_| {
                    dec.pos
                        .error_exit(type_mis(&mut self.type_var_map, expected_type, &adt_type))
                });
                let variant_members = self.adts
                    .members_with_inst_of_variant_with_name(dec.constr.s, adt_inst)
                    .expect("ICE: No members with inst of variant with name in infer_pattern");
                let (n_subs, n_members) = (dec.subpatts.len(), variant_members.len());
                if n_subs != n_members {
                    dec.pos.error_exit(ConstrWrongNumArgs {
                        expected: n_members,
                        found: n_subs,
                    })
                }
                for (subpatt, member_type) in dec.subpatts.iter_mut().zip(&variant_members) {
                    self.infer_pattern(subpatt, member_type);
                }
                typ
            }
        }
    }

    fn infer_case<'c>(
        &mut self,
        case: &'c mut Case<'s>,
        expected_patt_type: &Type<'s>,
        expected_body_type: &Type<'s>,
    ) -> (&'c Type<'s>, &'c Type<'s>) {
        case.patt_typ = self.infer_pattern(&mut case.patt, &expected_patt_type);
        for var in case.patt.variables() {
            self.push_var(var.ident.s, var.typ.clone())
        }
        self.infer_expr(&mut case.body, expected_body_type);
        for var in case.patt.variables() {
            self.pop_var(var.ident.s)
                .unwrap_or_else(|| panic!("ICE: binding gone from var_env in infer_match"));
        }
        (&case.patt_typ, case.body.get_type())
    }

    fn infer_match<'m>(&mut self, m: &'m mut Match<'s>, expected_type: &Type<'s>) -> &'m Type<'s> {
        let expected_expr_type = self.type_var_gen.gen_type_var();
        let expr_typ = self.infer_expr(&mut m.expr, &expected_expr_type);
        for case in &mut m.cases {
            self.infer_case(case, &expr_typ, expected_type);
        }
        m.typ = expected_type.clone();
        &m.typ
    }

    // The type of an expression will only be inferred once
    fn infer_expr(&mut self, expr: &mut Expr<'s>, expected_type: &Type<'s>) -> Type<'s> {
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
            Expr::New(ref mut n) => self.infer_new(n, expected_type).clone(),
            Expr::Match(ref mut m) => self.infer_match(m, expected_type).clone(),
        }
    }
}

fn assert_externs_monomorphic(externs: &BTreeMap<&str, ExternDecl>) {
    for ext in externs.values() {
        if !ext.typ.is_monomorphic() {
            ext.pos
                .error_exit("Type of external declaration must be monomorphic")
        }
    }
}

pub fn infer_types(ast: &mut Ast, type_var_generator: &mut TypeVarGen) {
    assert_externs_monomorphic(&ast.externs);
    let mut inferrer = Inferrer::new(&mut ast.externs, &mut ast.adts, type_var_generator);

    inferrer.infer_bindings(&mut ast.globals);

    // Apply all substitutions recursively to get rid of reduntant, indirect type variables
    for binding in ast.globals.bindings_mut() {
        binding.sig.body = subst(&binding.sig.body, &mut inferrer.type_var_map);
        subst_expr(&mut binding.val, &mut inferrer.type_var_map);
    }

    // Map monomorphic instantiations of variables to monomorphization of definitions
    monomorphize_defs_of_insts(&mut ast.globals);
}
