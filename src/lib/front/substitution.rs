use std::collections::BTreeMap;
use lib::front::ast::*;

fn subst_poly<'src>(p: &Poly<'src>, s: &mut BTreeMap<TVar<'src>, Type<'src>>) -> Poly<'src> {
    let shadowed_mappings = p.params
        .iter()
        .filter_map(|(param_v, _)| s.remove(&param_v).map(|t| (*param_v, t)))
        .collect::<Vec<_>>();
    let substituted = subst(&p.body, s);
    s.extend(shadowed_mappings);
    Poly {
        params: p.params.clone(),
        body: substituted,
    }
}

fn subst_type_func<'src>(
    f: &TypeFunc<'src>,
    s: &mut BTreeMap<TVar<'src>, Type<'src>>,
) -> TypeFunc<'src> {
    match *f {
        TypeFunc::Const(c) => TypeFunc::Const(c),
        TypeFunc::Poly(ref p) => TypeFunc::Poly(subst_poly(p, s)),
    }
}

/// Apply substitutions in `s` to free type variables in `t`
pub fn subst<'src>(t: &Type<'src>, s: &mut BTreeMap<TVar<'src>, Type<'src>>) -> Type<'src> {
    match *t {
        Type::Var(ref tv) => s.get(&tv)
            .cloned()
            .map(|t2| subst(&t2, s))
            .unwrap_or(t.clone()),
        Type::App(ref c, ref ts) => Type::App(
            Box::new(subst_type_func(c, s)),
            ts.iter().map(|t2| subst(t2, s)).collect(),
        ),
        Type::Poly(ref p) => Type::Poly(Box::new(subst_poly(p, s))),
        _ => t.clone(),
    }
}

/// Apply substitutions in `s` to type variables in types in `e`
pub fn subst_expr<'src>(e: &mut Expr<'src>, s: &mut BTreeMap<TVar<'src>, Type<'src>>) {
    match *e {
        Expr::NumLit(ref mut n) => n.typ = subst(&n.typ, s),
        Expr::Variable(ref mut bnd) => bnd.typ = subst(&bnd.typ, s),
        Expr::App(ref mut app) => {
            subst_expr(&mut app.func, s);
            subst_expr(&mut app.arg, s);
            app.typ = subst(&app.typ, s);
        }
        Expr::If(ref mut cond) => {
            subst_expr(&mut cond.predicate, s);
            subst_expr(&mut cond.consequent, s);
            subst_expr(&mut cond.alternative, s);
            cond.typ = subst(&cond.typ, s);
        }
        Expr::Lambda(ref mut l) => {
            subst_expr(&mut l.body, s);
            l.typ = subst(&l.typ, s);
        }
        Expr::Let(ref mut l) => {
            for binding in l.bindings.bindings_mut() {
                binding.sig = subst_poly(&binding.sig, s);
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
        Expr::Car(ref mut c) => {
            c.typ = subst(&c.typ, s);
            subst_expr(&mut c.expr, s);
        }
        Expr::Cdr(ref mut c) => {
            c.typ = subst(&c.typ, s);
            subst_expr(&mut c.expr, s);
        }
        Expr::Cast(ref mut c) => {
            c.typ = subst(&c.typ, s);
            subst_expr(&mut c.expr, s);
        }
        Expr::New(ref mut n) => for member in &mut n.members {
            subst_expr(member, s);
        },
        Expr::Match(ref mut m) => {
            subst_expr(&mut m.expr, s);
            m.typ = subst(&m.typ, s);
            for case in &mut m.cases {
                case.patt_typ = subst(&case.patt_typ, s);
                for v in case.patt.variables_mut() {
                    v.typ = subst(&v.typ, s);
                }
                subst_expr(&mut case.body, s);
            }
        }
        Expr::Nil(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}
