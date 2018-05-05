use lib::front::ast::*;

pub type Instantiations<'src> = BTreeSet<(Vec<Type<'src>>, Type<'src>)>;
pub type FreeVarInsts<'src> = BTreeMap<&'src str, Instantiations<'src>>;

/// Returns the unit set of the single element `x`
fn set_of<T: cmp::Ord>(x: T) -> BTreeSet<T> {
    once(x).collect()
}

/// Returns the map of `{k} -> {v}`
fn map_of<K: cmp::Ord, V>(k: K, v: V) -> BTreeMap<K, V> {
    once((k, v)).collect()
}

pub fn free_vars_in_exprs<'a, 'src: 'a, T>(es: T) -> FreeVarInsts<'src>
where
    T: IntoIterator<Item = &'a Expr<'src>>,
{
    let mut fvs = BTreeMap::new();
    for (k, v) in es.into_iter().flat_map(|e2| free_vars_in_expr(e2)) {
        fvs.entry(k).or_insert(BTreeSet::new()).extend(v)
    }
    fvs
}

/// Returns a map of the free variables in `e`, where each variable name is mapped to the
/// instantiations of the free variable in `e`
pub fn free_vars_in_expr<'src>(e: &Expr<'src>) -> FreeVarInsts<'src> {
    use self::ast::Expr::*;
    match *e {
        Nil(_) | NumLit(_) | StrLit(_) | Bool(_) => FreeVarInsts::new(),
        Variable(ref v) => {
            map_of(
                v.ident.s,
                set_of((
                    v.typ.get_inst_args().unwrap_or(&[]).to_vec(),
                    // Apply instantiation to type to remove wrapping `App`
                    v.typ.canonicalize(),
                )),
            )
        }
        App(box ref a) => free_vars_in_exprs([&a.func, &a.arg].iter().cloned()),
        If(ref i) => free_vars_in_exprs(
            [&i.predicate, &i.consequent, &i.alternative]
                .iter()
                .cloned(),
        ),
        Lambda(box ref l) => free_vars_in_lambda(l),
        Let(box ref l) => {
            let mut es = vec![&l.body];
            for binding in l.bindings.bindings() {
                if binding.typ.is_monomorphic() {
                    es.push(&binding.val)
                } else {
                    es.extend(binding.mono_insts.values())
                }
            }
            let mut fvs = free_vars_in_exprs(es.iter().cloned());
            for b in l.bindings.bindings() {
                fvs.remove(b.ident.s);
            }
            fvs
        }
        TypeAscript(_) => panic!("free_vars_in_expr encountered TypeAscript"),
        Cons(box ref c) => free_vars_in_exprs([&c.car, &c.cdr].iter().cloned()),
        Car(box ref c) => free_vars_in_expr(&c.expr),
        Cdr(box ref c) => free_vars_in_expr(&c.expr),
        Cast(ref c) => free_vars_in_expr(&c.expr),
        New(ref n) => free_vars_in_exprs(&n.members),
    }
}

/// Returns a map of the free variables in `e`, where each variable name is mapped to the
/// instantiations of the free variable in `e`
pub fn free_vars_in_lambda<'src>(lam: &Lambda<'src>) -> FreeVarInsts<'src> {
    let mut free_vars = free_vars_in_expr(&lam.body);
    free_vars.remove(lam.param_ident.s);
    free_vars
}

/// Generate a new variable for use in a binding, that does not occur in `not_in_expr`
pub fn new_variable<'s>(not_in_expr: &Expr<'s>) -> String {
    let frees = free_vars_in_expr(not_in_expr);
    (0..)
        .map(|i| format("_{}", i))
        .find(|s| !frees.contains_key(&s))
        .expect("ICE: Out of variable names in new_variable")
}
