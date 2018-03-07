use std::collections::BTreeMap;
use lib::front::ast::*;

fn subst_poly<'src>(p: &Poly<'src>, s: &mut BTreeMap<u64, Type<'src>>) -> Poly<'src> {
    let shadowed_mappings = p.params
        .iter()
        .filter_map(|tv| s.remove(&tv.id).map(|t| (tv.id, t)))
        .collect::<Vec<_>>();
    let substituted = subst(&p.body, s);
    s.extend(shadowed_mappings);
    Poly {
        params: p.params.clone(),
        body: substituted,
    }
}

fn subst_type_func<'src>(f: &TypeFunc<'src>, s: &mut BTreeMap<u64, Type<'src>>) -> TypeFunc<'src> {
    match *f {
        TypeFunc::Const(c) => TypeFunc::Const(c),
        TypeFunc::Poly(ref p) => TypeFunc::Poly(subst_poly(p, s)),
    }
}

/// Apply substitutions in `s` to free type variables in `t`
pub fn subst<'src>(t: &Type<'src>, s: &mut BTreeMap<u64, Type<'src>>) -> Type<'src> {
    match *t {
        Type::Var(ref tv) => s.get(&tv.id)
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
pub fn subst_expr<'src>(e: &mut Expr<'src>, s: &mut BTreeMap<u64, Type<'src>>) {
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
            l.param_type = subst(&l.param_type, s);
            subst_expr(&mut l.body, s);
            l.typ = subst(&l.typ, s);
        }
        Expr::Let(ref mut l) => {
            for binding in l.bindings.bindings_mut() {
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
        Expr::OfVariant(ref mut x) => subst_expr(&mut x.expr, s),
        Expr::AsVariant(ref mut x) => subst_expr(&mut x.expr, s),
        Expr::Nil(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}
