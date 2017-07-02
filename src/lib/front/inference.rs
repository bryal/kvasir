//! Type inference

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
use lib::collections::ScopeStack;
use lib::front::error_exit;
use lib::front::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};
use std::mem::{replace, swap};
use std::iter;
use itertools::{zip, Itertools};

enum InferenceErr<'p, 'src: 'p> {
    /// Type mismatch. (expected, found)
    TypeMis(&'p Type<'src>, &'p Type<'src>),
    /// Type mismatch with specified mismatching nodes
    TypeMisSub {
        expected: &'p Type<'src>,
        found: &'p Type<'src>,
        sub_expected: &'p Type<'src>,
        sub_found: &'p Type<'src>,
    },
    ArmsDiffer(&'p Type<'src>, &'p Type<'src>),
}

impl<'src, 'p> Display for InferenceErr<'src, 'p> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeMis(expected, found) => {
                write!(
                    f,
                    "Type mismatch. Expected `{}`, found `{}`",
                    expected,
                    found
                )
            }
            TypeMisSub {
                expected,
                found,
                sub_expected,
                sub_found,
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
            ArmsDiffer(c, a) => {
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

/// Apply substitutions in `s` to type variables in `t`
fn subst<'src>(t: &Type<'src>, s: &mut HashMap<u64, Type<'src>>) -> Type<'src> {
    match *t {
        Type::Var(ref n) => {
            s.get(n).cloned().map(|t2| subst(&t2, s)).unwrap_or(
                t.clone(),
            )
        }
        Type::App(c, ref ts) => Type::App(c, ts.iter().map(|t2| subst(t2, s)).collect()),
        Type::Scheme(ref is, ref u) => {
            let shadowed_mappings = is.iter()
                .filter_map(|i| s.remove(i).map(|t| (*i, t)))
                .collect::<Vec<_>>();
            let substituted = subst(u, s);
            s.extend(shadowed_mappings);
            Type::Scheme(is.clone(), Box::new(substituted))
        }
        _ => t.clone(),
    }
}

/// Apply substitutions in `s` to type variables in types in `e`
fn subst_expr<'src>(e: &mut Expr<'src>, s: &mut HashMap<u64, Type<'src>>) {
    match *e {
        Expr::Variable(ref mut bnd) => bnd.typ = subst(&bnd.typ, s),
        Expr::Call(ref mut call) => {
            subst_expr(&mut call.func, s);
            subst_expr(&mut call.arg, s);
            call.typ = subst(&call.typ, s);
        }
        Expr::If(ref mut cond) => {
            subst_expr(&mut cond.predicate, s);
            subst_expr(&mut cond.consequent, s);
            subst_expr(&mut cond.alternative, s);
            cond.typ = subst(&cond.typ, s);
        }
        Expr::Lambda(ref mut l) => {
            l.param_type = subst(&l.param_type, s);
            subst_expr(&mut l.body, s);
            l.typ = subst(&l.typ, s);
        }
        Expr::Let(ref mut l) => {
            for binding in &mut l.bindings {
                binding.typ = subst(&binding.typ, s);
                subst_expr(&mut binding.val, s);
            }
            subst_expr(&mut l.body, s);
            l.typ = subst(&l.typ, s);
        }
        Expr::TypeAscript(ref mut a) => {
            a.typ = subst(&a.typ, s);
            subst_expr(&mut a.expr, s);
        }
        Expr::Cons(ref mut c) => {
            c.typ = subst(&c.typ, s);
            subst_expr(&mut c.car, s);
            subst_expr(&mut c.cdr, s);
        }
        _ => (),
    }
}

/// Returns whether type variable `t` occurs in type `u` with substitutions `s`
///
/// Useful to check for circular type variable mappings
fn occurs_in(t: u64, u: &Type, s: &HashMap<u64, Type>) -> bool {
    match *u {
        Type::Var(n) if t == n => true,
        Type::Var(n) => s.get(&n).map(|u2| occurs_in(t, u2, s)).unwrap_or(false),

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

struct TypeVarGen(u64);

impl TypeVarGen {
    /// Generates a new, unique type variable
    fn new_type_var<'src>(&mut self) -> Type<'src> {
        let n = self.0;
        self.0 += 1;
        Type::Var(n)
    }
}

struct Inferer<'exts, 'src: 'exts> {
    /// The environment of variables from let-bindings and function-parameters
    var_env: HashMap<&'src str, Vec<Type<'src>>>,
    /// Declarations of external variables
    externs: &'exts HashMap<&'src str, ExternDecl<'src>>,
    /// A map of free type variables to their instantiations
    type_var_map: HashMap<u64, Type<'src>>,
    /// Counter for generation of unique type variable ids
    type_var_gen: TypeVarGen,
}

impl<'exts, 'src: 'exts> Inferer<'exts, 'src> {
    fn with_externs(externs: &'exts HashMap<&'src str, ExternDecl<'src>>) -> Self {
        Inferer {
            var_env: HashMap::new(),
            externs: externs,
            type_var_map: HashMap::new(),
            type_var_gen: TypeVarGen(0),
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

    /// Returns an iterator of all type variables that occur in `t`
    ///
    /// May contain duplicates. Collect into a set or such for uniqueness
    fn get_type_vars<'t>(&'t self, t: &'t Type<'src>) -> Box<Iterator<Item = u64> + 't> {
        match *t {
            Type::Var(n) => {
                self.type_var_map
                    .get(&n)
                    .map(|u| {
                        if occurs_in(n, u, &self.type_var_map) {
                            // NOTE: Shouldn't be able to happen if no bugs right?
                            panic!("ICE: in get_type_vars: t occurs in u")
                        } else {
                            self.get_type_vars(u)
                        }
                    })
                    .unwrap_or(Box::new(iter::once(n)))
            }
            Type::App(_, ref ts) => Box::new(ts.iter().flat_map(move |t2| self.get_type_vars(t2))),
            Type::Scheme(ref is, ref u) => {
                let mut set = self.get_type_vars(u).collect::<HashSet<_>>();
                for i in is {
                    set.remove(i);
                }
                Box::new(set.into_iter())
            }
            _ => Box::new(iter::empty()),
        }
    }

    // TODO: Separate polytypes from normal types?
    /// Instantiate a polymorphic value
    fn instantiate(&mut self, t: &Type<'src>) -> Type<'src> {
        match *t {
            Type::Scheme(ref is, ref u) => {
                let type_var_gen = &mut self.type_var_gen;
                self.type_var_map.extend(
                    is.iter()
                        .map(|&i| (i, type_var_gen.new_type_var()))
                        .collect::<Vec<_>>(),
                );
                let t_inst = subst(&u, &mut self.type_var_map);
                for i in is {
                    self.type_var_map.remove(i);
                }
                t_inst
            }
            _ => t.clone(),
        }
    }

    /// Generalize `t` to a polytype by quantifying monotype variables
    /// that are not bound in the context
    fn generalize(&mut self, t: &Type<'src>) -> Type<'src> {
        let env_type_vars = self.var_env
            .iter()
            .flat_map(|(_, v)| v.iter())
            .flat_map(|v_t| self.get_type_vars(v_t))
            .collect::<HashSet<_>>();
        let t_type_vars = self.get_type_vars(t).unique();
        let unbounds = t_type_vars
            .filter(|tv| !env_type_vars.contains(tv))
            .collect();
        Type::Scheme(unbounds, Box::new(t.clone()))
    }

    // TODO: Should this algorithm introduce type variables on `Uninferred`?
    // TODO: Instantiation of circular type. Can it happen?
    /// Unify two types
    ///
    /// Introduce type variables and generate substitutions such that the two types
    /// are equivalent in the resulting environment.
    /// On success, returns the unification. On failure, returns the conflicting nodes
    fn unify(
        &mut self,
        a: &Type<'src>,
        b: &Type<'src>,
    ) -> Result<Type<'src>, (Type<'src>, Type<'src>)> {
        use self::Type::*;
        match (a, b) {
            (&Var(ref n), _) if self.type_var_map.contains_key(n) => {
                let a2 = self.type_var_map[n].clone();
                self.unify(&a2, b)
            }
            (_, &Var(ref m)) if self.type_var_map.contains_key(m) => {
                let b2 = self.type_var_map[m].clone();
                self.unify(a, &b2)
            }
            (&Var(n), &Var(m)) if n == m => Ok(Var(n)),
            (&Var(n), &App(c, ref ts)) => {
                let news = (0..ts.len())
                    .map(|_| self.type_var_gen.new_type_var())
                    .collect();
                self.type_var_map.insert(n, App(c, news));
                self.unify(a, b)
            }
            (&Uninferred, _) => Ok(b.clone()),
            (_, &Uninferred) => Ok(a.clone()),
            (&Var(n), _) => {
                self.type_var_map.insert(n, b.clone());
                Ok(b.clone())
            }
            (_, &Var(_)) => self.unify(b, a),
            (&App(c1, ref ts1), &App(c2, ref ts2)) if c1 == c2 && ts1.len() == ts2.len() => {
                zip(ts1, ts2)
                    .map(|(t1, t2)| self.unify(t1, t2))
                    .collect::<Result<_, _>>()
                    .map(|us| App(c1, us))
            }
            // TODO: Can this happen?
            (&Scheme(_, _), _) |
            (_, &Scheme(_, _)) => panic!("ICE: unifying type scheme: `{}` U `{}`", a, b),
            (_, _) if a == b => Ok(a.clone()),
            _ => Err((a.clone(), b.clone())),
        }
    }

    /// Check that the expected type of a nil expression is unifiable with the nil type
    fn infer_nil(&mut self, nil: &mut Nil<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_NIL).unwrap_or_else(|_| {
            nil.pos.error_exit(TypeMis(expected_type, &TYPE_NIL))
        })
    }

    /// Check that the expected type of a string literal is unifiable with the string type
    fn infer_str_lit(&mut self, lit: &mut StrLit<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_STRING).unwrap_or_else(
            |_| {
                lit.pos.error_exit(TypeMis(expected_type, &TYPE_STRING))
            },
        )
    }

    /// Check that the expected type of a boolean literal is unifiable with the boolean type
    fn infer_bool(&mut self, b: &mut Bool<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_BOOL).unwrap_or_else(|_| {
            b.pos.error_exit(TypeMis(expected_type, &TYPE_BOOL))
        })
    }

    /// Infer the type of a numeric literal
    ///
    /// Type can be one of a selection of numeric types.
    fn infer_num_lit<'n>(
        &mut self,
        lit: &'n mut NumLit<'src>,
        expected_type: &Type<'src>,
    ) -> &'n Type<'src> {
        let num_type = [
            // Int must be highest since it is the "default" and should match first,
            // if expected type is type variable or somesuch
            "Int",
            "Int64",
            "Int32",
            "Int16",
            "Int8",
            "UInt",
            "UInt64",
            "UInt32",
            "UInt16",
            "UInt8",
            "Float64",
            "Float32",
        ].iter()
            .map(|s| self.unify(expected_type, &Type::Const(s)))
            .filter(Result::is_ok)
            .next()
            .unwrap_or_else(|| {
                lit.pos.error_exit(format!(
                    "Type mismatch. Expected `{}`, found numeric literal",
                    expected_type
                ))
            })
            .unwrap();

        lit.typ = num_type;
        &lit.typ
    }

    /// Infer the type of a variable
    ///
    /// If the variable does not refer to an extern, instantiate the variable
    /// and unify with expected type. If it does refer to an extern,
    /// unify type of extern with expected type.
    fn infer_variable<'v>(
        &mut self,
        var: &'v mut Variable<'src>,
        expected_type: &Type<'src>,
    ) -> &'v Type<'src> {
        if let Some(typ) = self.get_var(var.ident.s).cloned() {
            // Either not an extern, or shadowing an extern. I.e. a lambda parameter or let binding
            let instantiation = self.instantiate(&typ);
            var.typ = self.unify(expected_type, &instantiation).unwrap_or_else(
                |_| {
                    var.ident.pos.error_exit(format!(
                        "Variable of type `{}` cannot be instantiated to expected type `{}`",
                        typ,
                        expected_type
                    ))
                },
            );
            &var.typ
        } else if let Some(ext) = self.externs.get(var.ident.s) {
            // An extern. Check that type of extern is unifiable with expected type
            var.typ = self.unify(expected_type, &ext.typ).unwrap_or_else(
                |(e, f)| {
                    var.ident.pos.error_exit(TypeMisSub {
                        expected: expected_type,
                        found: &ext.typ,
                        sub_expected: &e,
                        sub_found: &f,
                    })
                },
            );
            &var.typ
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
    fn infer_call<'c>(
        &mut self,
        call: &'c mut Call<'src>,
        expected_type: &Type<'src>,
    ) -> &'c Type<'src> {
        let func_type = self.infer_expr(
            &mut call.func,
            &Type::new_func(Type::Uninferred, Type::Uninferred),
        );
        let arg_type = self.infer_expr(&mut call.arg, &Type::Uninferred);
        let (func_arg_type, func_ret_type) = func_type.get_func().expect(
            "ICE: func_type was not func type in infer_call",
        );
        self.unify(func_arg_type, &arg_type).unwrap_or_else(
            |(e, f)| {
                call.arg.pos().error_exit(TypeMisSub {
                    expected: func_arg_type,
                    found: &arg_type,
                    sub_expected: &e,
                    sub_found: &f,
                })
            },
        );
        let ret_unification = self.unify(expected_type, func_ret_type).unwrap_or_else(
            |(e, f)| {
                call.pos.error_exit(TypeMisSub {
                    expected: expected_type,
                    found: func_ret_type,
                    sub_expected: &e,
                    sub_found: &f,
                })
            },
        );
        call.typ = ret_unification;
        &call.typ
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
                    ArmsDiffer(&consequent_type, &alternative_type),
                )
            });
        &cond.typ
    }

    /// Infer types for a lambda
    fn infer_lambda<'l>(
        &mut self,
        mut lam: &'l mut Lambda<'src>,
        expected_type: &Type<'src>,
    ) -> &'l Type<'src> {
        // Infer type of param by adding it to the environment and applying constraints based on
        // how it is used during inference of lambda body.

        let param_type = self.type_var_gen.new_type_var();
        let body_type = self.type_var_gen.new_type_var();
        let func_type = Type::new_func(param_type.clone(), body_type);
        let (expected_param_type, expected_body_type) = self.unify(expected_type, &func_type)
            .unwrap_or_else(|_| lam.pos.error_exit(TypeMis(expected_type, &func_type)))
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

    // TODO: Add indirect recursion
    // TODO: Make order-independent
    /// Infer types for bindings of a let-form and push them to the environment.
    fn infer_bindings(&mut self, bindings: &mut [Binding<'src>]) {
        for binding in bindings {
            let ascribed_type = binding.val.remove_type_ascription().unwrap_or(
                Type::Uninferred,
            );
            let val_type = self.type_var_gen.new_type_var();
            let expected_type = self.unify(&val_type, &ascribed_type).unwrap();

            // Only allow recursion for functions. Stuff like `let a = a + 1`
            // can't be compiled correctly without laziness.
            if let Expr::Lambda(_) = binding.val {
                // Add binding being inferred to env to allow recursion
                self.push_var(binding.ident.s, expected_type.clone());

                self.infer_expr(&mut binding.val, &expected_type);

                // Remove binding from env to get only surrounding env
                self.pop_var(binding.ident.s).unwrap_or_else(|| {
                    panic!("ICE: binding gone from var_env in infer_let_bindings")
                });
            } else {
                self.infer_expr(&mut binding.val, &expected_type);
            }

            // For binding, create type scheme with type variables found in binding
            // body and not in surrounding environment as type parameters
            binding.typ = self.generalize(&expected_type);
            self.push_var(binding.ident.s, binding.typ.clone());
        }
    }

    fn infer_let<'l>(
        &mut self,
        let_: &'l mut Let<'src>,
        expected_type: &Type<'src>,
    ) -> &'l Type<'src> {
        self.infer_bindings(&mut let_.bindings);
        let_.typ = self.infer_expr(&mut let_.body, expected_type).clone();

        for name in let_.bindings.iter().map(|b| b.ident.s) {
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
                    ascr_pos.error_exit(TypeMis(expected_type, &ascribed))
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
        let arbitrary_cons_type = Type::new_cons(Type::Uninferred, Type::Uninferred);
        let expected_type2 = self.unify(expected_type, &arbitrary_cons_type)
            .unwrap_or_else(|_| {
                cons.pos.error_exit(
                    TypeMis(expected_type, &arbitrary_cons_type),
                )
            });
        let (expected_car_type, expected_cdr_type) = expected_type2.get_cons().expect(
            "ICE: expected type not cons in infer_cons ",
        );
        let car_type = self.infer_expr(&mut cons.car, expected_car_type);
        let cdr_type = self.infer_expr(&mut cons.cdr, expected_cdr_type);
        cons.typ = Type::new_cons(car_type, cdr_type);
        &cons.typ
    }

    // The type of an expression will only be inferred once
    fn infer_expr(&mut self, expr: &mut Expr<'src>, expected_type: &Type<'src>) -> Type<'src> {
        match *expr {
            Expr::Nil(ref mut nil) => self.infer_nil(nil, expected_type),
            Expr::StrLit(ref mut l) => self.infer_str_lit(l, expected_type),
            Expr::Bool(ref mut b) => self.infer_bool(b, expected_type),
            Expr::NumLit(ref mut l) => self.infer_num_lit(l, expected_type).clone(),
            Expr::Variable(ref mut var) => self.infer_variable(var, expected_type).clone(),
            Expr::Call(ref mut call) => self.infer_call(call, expected_type).clone(),
            Expr::If(ref mut cond) => self.infer_if(cond, expected_type).clone(),
            Expr::Lambda(ref mut lam) => self.infer_lambda(lam, expected_type).clone(),
            Expr::Let(ref mut l) => self.infer_let(l, expected_type).clone(),
            Expr::TypeAscript(_) => self.infer_type_ascription(expr, expected_type),
            Expr::Cons(ref mut cons) => self.infer_cons(cons, expected_type).clone(),
        }
    }
}

pub fn infer_types(module: &mut Module) {
    println!("EXTERNS:\n{:#?}\n\n", module.externs);

    if let Some(ref mut main) = module.main {
        let mut inferrer = Inferer::with_externs(&mut module.externs);
        inferrer.infer_bindings(&mut module.globals);
        let expected_main_type = Type::new_func(TYPE_NIL.clone(), TYPE_NIL.clone());
        // Add binding being inferred to env to allow recursion
        inferrer.push_var(main.ident.s, expected_main_type.clone());
        main.typ = inferrer.infer_expr(&mut main.val, &expected_main_type);

        println!("BEFORE SUBST INFERRED GLOBALS:\n{:#?}\n", module.globals);
        println!("BEFORE SUBST INFERRED MAIN:\n{:#?}\n", main);

        // Apply all substitutions to get rid of reduntant type variables
        for binding in &mut module.globals {
            binding.typ = subst(&binding.typ, &mut inferrer.type_var_map);
            subst_expr(&mut binding.val, &mut inferrer.type_var_map);
        }
        main.typ = subst(&main.typ, &mut inferrer.type_var_map);
        subst_expr(&mut main.val, &mut inferrer.type_var_map);

        println!("AFTER SUBST INFERRED GLOBALS:\n{:#?}\n", module.globals);
        println!("AFTER SUBST INFERRED MAIN:\n{:#?}\n", main);

        println!("TYPE VAR MAPPING:\n{:?}\n", inferrer.type_var_map);
    } else {
        // `main` required as entry point for executable target
        error_exit(
            "`main` function not found.\n\
             A `main` function is required as entry point for executable target",
        )
    }
}
