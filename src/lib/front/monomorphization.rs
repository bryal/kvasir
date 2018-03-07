use itertools::zip;
use std::collections::BTreeMap;
use std::path;
use lib::collections::*;
use lib::front::*;
use lib::front::ast::*;
use lib::front::substitution::*;

/// If `var` is an instantiation of a polymorphic value and monomorphization
/// does not already exist for this instantiation type, generate a
/// monomorphization and return the monomorphisized definition
fn monomorphize_def_of_inst<'src>(
    var: &mut Variable<'src>,
    env: &mut ScopeStack<&str, Binding<'src>>,
) -> Option<(Vec<Type<'src>>, Expr<'src>)> {
    if let Type::App(ref f, ref mut ts) = var.typ {
        // In application of poly function to poly args, any type can be used
        // for the args during codegen, with the constraint that a Num arg must
        // be numeric. As such, default args of (application of poly function to poly args)
        // to Int64
        *ts = ts.iter()
            .map(|t| {
                if !t.is_monomorphic() {
                    Type::Const("Int64", None)
                } else {
                    t.clone()
                }
            })
            .collect::<Vec<_>>();
        if let TypeFunc::Poly(ref p) = **f {
            // An application of a polytype =>
            //   it's an instantiation to generate monomorphization for
            let b = env.get(var.ident.s).unwrap();
            if !b.mono_insts.contains_key(&*ts) {
                // The monomorphization does not already exist
                let mut s = zip(&p.params, &*ts)
                    .map(|(param, t)| (param.id, t.clone()))
                    .collect();
                let mut def_mono = b.val.clone();
                subst_expr(&mut def_mono, &mut s);
                return Some((ts.clone(), def_mono));
            }
        }
    } else if !var.typ.is_monomorphic() {
        // If, in a monomorphic instantiation, the variable can be of any type:
        // consistently default to generating it as Int64
        var.typ = Type::Const("Int64", None)
    }
    // Either definition is already monomorphic to begin with,
    // or it is polymorphic, but monomorphization has already been generated
    None
}

/// Monomorphize definitions for monomorphic instantiations of variables in `expr`
fn monomorphize_defs_of_insts_in_expr<'src>(
    e: &mut Expr<'src>,
    env: &mut ScopeStack<&'src str, Binding<'src>>,
) {
    match *e {
        Expr::NumLit(ref mut l) => {
            if !l.typ.is_monomorphic() {
                l.typ = Type::Const("Int64", None);
            }
        }
        Expr::Variable(ref mut var) => {
            if let Some((arg_ts, mut def_mono)) = monomorphize_def_of_inst(var, env) {
                // Insert dummy monomorphization as a tag to show that monomorphization
                // already has been done, but we still need `def_mono` to continue
                // our recursive monomorphization
                {
                    let dummy_expr = Expr::Nil(Nil {
                        pos: SrcPos::new_pos(path::Path::new(""), "", 0),
                    });
                    let b = env.get_mut(var.ident.s).unwrap();
                    b.mono_insts.insert(arg_ts.clone(), dummy_expr);
                }

                // Recursively generate monomorphizations for now-monomorphic
                // instantiations in `def_mono`
                let h = env.get_height(var.ident.s).unwrap();
                let above = env.split_off(h + 1);
                monomorphize_defs_of_insts_in_expr(&mut def_mono, env);
                env.extend(above);

                let b = env.get_mut(var.ident.s).unwrap();
                *b.mono_insts.get_mut(&arg_ts).unwrap() = def_mono;
            }
        }
        Expr::App(ref mut app) => {
            monomorphize_defs_of_insts_in_expr(&mut app.func, env);
            monomorphize_defs_of_insts_in_expr(&mut app.arg, env);
        }
        Expr::If(ref mut cond) => {
            monomorphize_defs_of_insts_in_expr(&mut cond.predicate, env);
            monomorphize_defs_of_insts_in_expr(&mut cond.consequent, env);
            monomorphize_defs_of_insts_in_expr(&mut cond.alternative, env);
        }
        Expr::Lambda(ref mut lam) => {
            monomorphize_defs_of_insts_in_expr(&mut lam.body, env);
        }
        Expr::Let(box ref mut l) => {
            monomorphize_defs_of_insts_in_let(&mut l.bindings, &mut l.body, env)
        }
        Expr::TypeAscript(_) => unreachable!(),
        Expr::Cons(ref mut cons) => {
            monomorphize_defs_of_insts_in_expr(&mut cons.car, env);
            monomorphize_defs_of_insts_in_expr(&mut cons.cdr, env);
        }
        Expr::Car(ref mut c) => {
            monomorphize_defs_of_insts_in_expr(&mut c.expr, env);
        }
        Expr::Cdr(ref mut c) => {
            monomorphize_defs_of_insts_in_expr(&mut c.expr, env);
        }
        Expr::Cast(ref mut c) => {
            monomorphize_defs_of_insts_in_expr(&mut c.expr, env);
        }
        Expr::OfVariant(ref mut x) => monomorphize_defs_of_insts_in_expr(&mut x.expr, env),
        Expr::AsVariant(ref mut x) => monomorphize_defs_of_insts_in_expr(&mut x.expr, env),
        Expr::Nil(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}

/// Monomorphize definitions for monomorphic instantiations of variables in `bindings`
fn monomorphize_defs_of_insts_in_let<'src>(
    bindings: &mut TopologicallyOrderedDependencyGroups<'src>,
    body: &mut Expr<'src>,
    env: &mut ScopeStack<&'src str, Binding<'src>>,
) {
    let mut monos = BTreeMap::new();
    let mut bindings_flat_map = BTreeMap::new();
    for b in bindings.bindings() {
        if b.typ.is_monomorphic() {
            monos.insert(b.ident.s, b.val.clone());
        }
        bindings_flat_map.insert(b.ident.s, b.clone());
    }
    env.push(bindings_flat_map);

    for (_, mut def) in &mut monos {
        monomorphize_defs_of_insts_in_expr(&mut def, env);
    }
    monomorphize_defs_of_insts_in_expr(body, env);

    for b in bindings.bindings_mut() {
        if let Some(upd_def) = monos.remove(b.ident.s) {
            b.val = upd_def;
        } else if let Some(upd_bnd) = env.remove(b.ident.s) {
            *b = upd_bnd
        }
    }
    env.pop().unwrap();
}

/// Monomorphize definitions for monomorphic instantiations of variables in `bindings`
pub fn monomorphize_defs_of_insts<'src>(globals: &mut TopologicallyOrderedDependencyGroups<'src>) {
    let mut dummy_body = Expr::Nil(Nil {
        pos: SrcPos::new_pos(path::Path::new(""), "", 0),
    });
    monomorphize_defs_of_insts_in_let(globals, &mut dummy_body, &mut ScopeStack::new());
}
