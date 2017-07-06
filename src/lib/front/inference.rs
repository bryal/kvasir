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
use lib::front::*;
use lib::front::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};
use std::iter::{once, FromIterator};
use std::path;
use itertools::{zip, repeat_call, Itertools};

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

fn subst_poly<'src>(p: &Poly<'src>, s: &mut HashMap<u64, Type<'src>>) -> Poly<'src> {
    let shadowed_mappings = p.params
        .iter()
        .filter_map(|i| s.remove(i).map(|t| (*i, t)))
        .collect::<Vec<_>>();
    let substituted = subst(&p.body, s);
    s.extend(shadowed_mappings);
    Poly {
        params: p.params.clone(),
        body: substituted,
    }
}

fn subst_type_func<'src>(f: &TypeFunc<'src>, s: &mut HashMap<u64, Type<'src>>) -> TypeFunc<'src> {
    match *f {
        TypeFunc::Const(c) => TypeFunc::Const(c),
        TypeFunc::Poly(ref p) => TypeFunc::Poly(subst_poly(p, s)),
    }
}

/// Apply substitutions in `s` to free type variables in `t`
fn subst<'src>(t: &Type<'src>, s: &mut HashMap<u64, Type<'src>>) -> Type<'src> {
    match *t {
        Type::Var(ref n) => {
            s.get(n).cloned().map(|t2| subst(&t2, s)).unwrap_or(
                t.clone(),
            )
        }
        Type::App(ref c, ref ts) => {
            Type::App(
                Box::new(subst_type_func(c, s)),
                ts.iter().map(|t2| subst(t2, s)).collect(),
            )
        }
        Type::Poly(ref p) => Type::Poly(Box::new(subst_poly(p, s))),
        _ => t.clone(),
    }
}

/// Apply substitutions in `s` to type variables in types in `e`
fn subst_expr<'src>(e: &mut Expr<'src>, s: &mut HashMap<u64, Type<'src>>) {
    match *e {
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
            for (_, binding) in &mut l.bindings {
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

/// A representation of let-bindings that describes the dependencies of the bindings to each other
///
/// In a set of simultaneously defined bindings (i.e. the bindings of a let-form), bindings may
/// be defined in terms of each other. These relationships can be represented with a disjoint
/// union of directed, acyclic graphs where a node is a cyclic graph of recursively defined
/// bindings.
///
/// As the graphs are DAGs, the groups can be ordered topologically. Type inference is now simple.
/// We start at the end of the topological order and infer types group-wise in reverse order.
///
/// Within a cyclical group, we begin inference in an arbitrary definition. If a variable referring
/// to a binding within the group is encountered, recursively infer in the definition of that
/// variable and record the jump. If a variable referring to a binding is encountered that is
/// already in the jump stack, no more information can be gained from following the variable, so
/// just get the current type of the variable. When done inferring in a definition, do not
/// generalize the type. Only when the whole group has been inferred, generalize the types of the
/// definitions as a group. I.e., all bindings will have take the same type arguments.
///
/// # Example
///
/// The following definitions together constitute a single DAG
///
/// ```lisp
/// (define (id x)       ; Will be in a group on its own as no recursive definition in terms of
///   x)                 ; anything else. The group it constitutes is a leaf node in it's
///                      ; super-graph as it does not refer to anything n the same scope even
///                      ; non-recursively.
///
/// (define (id2 x)      ; No recursion, group on its own. Refers to `id` in same scope, so not a
///   (id x))            ; leaf group => higher in the topological order than group of `id`
///
/// (define (f n x)      ; `f` refers to `g` which refers to `f` and so on. They are mutually
///   (if (= n 0)        ; recursive, and as such, together they constitute a group. `g` further
///       x              ; refers to `id2` of the same scope, which implies that this group
///     (g (- n 1) x)))  ; is higher in the topoligical order than id2.
///
/// (define (g n x)
///   (id2 (f n x)))
/// ```
///
/// To infer types, we no start at the bottom of the topological order. `id` does not refer to
/// anything in the same scope, and is easily inferred to be of type `(for (t) (-> t t))`.
///
/// We move a step up in the order and get the group of `id2`. In `id2`, we simply instantiate
/// `id`s type of `(for (t) (-> t t))` with fresh type variables, and we get `(:: id (u))`
/// which implies `(: id (-> u u))`. `id2` is then generalized to `(for (u) (-> u u))`.
///
/// For the topmost group of `f` and `g`, we begin inference in `f`. We infer that the type of
/// `n` is `Int`, and that the type of the second argument, `x`, is the same as the return type.
/// Then we dive into `g`. Here we unify the parameter types of `(: f (-> Int a a))` with the types
/// of `g`s parameters `n` and `x`, and together with the return type of `f` and an instantiation
/// of `id2`, we get `(: g (-> Int a a))`. Finally, we return to `f` and then return from inference.
/// Now that all bindings in group has been inferred, we generalize. The only free type variable is
/// `a`. Both `f` and `g` are given the same type parameters, and the result is
/// `(: f (for (a) (-> Int a a)))` and `(: g (for (a) (-> Int a a)))`.
struct TopologicallyOrderedDependencyGroups<'src>(Vec<Group<'src>>);

/// Returns a set of all siblings being referred to in this expression
fn sibling_refs<'src>(e: &Expr<'src>, siblings: &mut HashSet<&'src str>) -> HashSet<&'src str> {
    use self::Expr::*;
    match *e {
        Variable(ref v) => {
            if siblings.contains(v.ident.s) {
                once(v.ident.s).collect()
            } else {
                HashSet::new()
            }
        }
        App(ref app) => {
            [&app.func, &app.arg]
                .iter()
                .flat_map(|e2| sibling_refs(e2, siblings))
                .collect()
        }
        If(ref cond) => {
            [&cond.predicate, &cond.consequent, &cond.alternative]
                .iter()
                .flat_map(|e2| sibling_refs(e2, siblings))
                .collect()
        }
        Lambda(ref l) => {
            let shadowed = siblings.remove(l.param_ident.s);
            let refs = sibling_refs(&l.body, siblings);
            if shadowed {
                siblings.insert(l.param_ident.s);
            }
            refs
        }
        Let(ref l) => {
            let shadoweds = l.bindings
                .keys()
                .filter_map(|id| if siblings.remove(id) { Some(id) } else { None })
                .collect::<Vec<_>>();
            let refs = l.bindings
                .values()
                .map(|b| &b.val)
                .chain(once(&l.body))
                .flat_map(|e2| sibling_refs(e2, siblings))
                .collect();
            for s in shadoweds {
                siblings.insert(s);
            }
            refs
        }
        Cons(ref c) => {
            [&c.car, &c.cdr]
                .iter()
                .flat_map(|e2| sibling_refs(e2, siblings))
                .collect()
        }
        TypeAscript(ref a) => sibling_refs(&a.expr, siblings),
        Nil(_) | NumLit(_) | StrLit(_) | Bool(_) => HashSet::new(),
    }
}

fn circular_def_members_<'src>(
    start: &'src str,
    current: &'src str,
    siblings_out_refs: &HashMap<&str, HashSet<&'src str>>,
    visited: &mut HashSet<&'src str>,
) -> HashSet<&'src str> {
    if current == start && visited.contains(current) {
        once(current).collect()
    } else if visited.contains(current) {
        HashSet::new()
    } else {
        visited.insert(current);
        let mut members = HashSet::new();
        for next in &siblings_out_refs[current] {
            members.extend(circular_def_members_(
                start,
                next,
                siblings_out_refs,
                visited,
            ))
        }
        if !members.is_empty() {
            members.insert(current);
        }
        members
    }
}

/// Returns all members of the circular definition chain of `s`
///
/// If `s` is not a circular definition, return the empty set
fn circular_def_members<'src>(
    s: &'src str,
    siblings_out_refs: &HashMap<&str, HashSet<&'src str>>,
) -> HashSet<&'src str> {
    let mut visited = HashSet::new();
    circular_def_members_(s, s, siblings_out_refs, &mut visited)
}

enum Group<'src> {
    Circular(HashMap<&'src str, Binding<'src>>),
    Uncircular(&'src str, Binding<'src>),
}

impl<'src> Group<'src> {
    fn contains(&self, e: &str) -> bool {
        match *self {
            Group::Circular(ref xs) => xs.contains_key(e),
            Group::Uncircular(x, _) => e == x,
        }
    }

    fn iter_keys<'a>(&'a self) -> Box<Iterator<Item = &'src str> + 'a> {
        match *self {
            Group::Circular(ref xs) => Box::new(xs.keys().map(|s| *s)),
            Group::Uncircular(x, _) => Box::new(once(x)),
        }
    }

    fn into_iter(self) -> Box<Iterator<Item = (&'src str, Binding<'src>)> + 'src> {
        match self {
            Group::Circular(xs) => Box::new(xs.into_iter()),
            Group::Uncircular(x, b) => Box::new(once((x, b))),
        }
    }
}

/// Group sets of circularly referencing bindings together, to make
/// the inter-group relation acyclic.
fn group_by_circularity<'src>(
    mut bindings: HashMap<&'src str, Binding<'src>>,
    siblings_out_refs: &HashMap<&'src str, HashSet<&'src str>>,
) -> HashMap<usize, Group<'src>> {
    let mut n = 0;
    let mut groups = HashMap::<usize, Group>::new();
    for sibling in siblings_out_refs.keys() {
        if groups.values().any(|group| group.contains(sibling)) {
            // Already part of a group of circular defs
            continue;
        } else {
            let members = circular_def_members(sibling, &siblings_out_refs);
            if members.is_empty() {
                groups.insert(
                    n,
                    Group::Uncircular(sibling, bindings.remove(sibling).unwrap()),
                );
            } else {
                let group = members
                    .into_iter()
                    .map(|s| (s, bindings.remove(s).unwrap()))
                    .collect();
                groups.insert(n, Group::Circular(group));
            }
            n += 1
        }
    }
    groups
}

fn group_refs<'src>(
    group_n: usize,
    groups: &HashMap<usize, Group>,
    siblings_out_refs: &HashMap<&str, HashSet<&str>>,
) -> HashSet<usize> {
    let group = &groups[&group_n];
    group
        .iter_keys()
        .flat_map(|member| &siblings_out_refs[member])
        .filter(|out_ref| !group.contains(out_ref))
        .map(|out_ref| {
            groups
                .iter()
                .find(|&(_, ref group2)| group2.contains(out_ref))
                .map(|(n, _)| *n)
                .unwrap()
        })
        .collect()
}

fn topological_sort<'src>(
    mut groups: HashMap<usize, Group<'src>>,
    groups_out_refs: &HashMap<usize, HashSet<usize>>,
    mut groups_n_incoming: Vec<usize>,
) -> Vec<Group<'src>> {
    // Kahn's algorithm for topological sorting

    // Empty list that will contain the sorted elements
    let mut l = Vec::new();
    // Set of all nodes (by index) with no incoming edge
    let mut s = groups_n_incoming
        .iter()
        .enumerate()
        .filter(|&(_, n)| *n == 0)
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    while let Some(n) = s.pop() {
        l.push(groups.remove(&n).unwrap());
        for &m in &groups_out_refs[&n] {
            groups_n_incoming[m] -= 1;
            if groups_n_incoming[m] == 0 {
                s.push(m)
            }
        }
    }
    // If graph has edges left
    if groups_n_incoming.iter().any(|n| *n != 0) {
        panic!("ICE: from_flat_set: graph has at least one cycle")
    } else {
        l
    }
}

impl<'src> TopologicallyOrderedDependencyGroups<'src> {
    /// Build the dependency graph from a flat set of bindings
    fn from_flat_set(bindings: HashMap<&'src str, Binding<'src>>) -> Self {
        let mut siblings: HashSet<_> = bindings.keys().cloned().collect();
        let siblings_out_refs: HashMap<_, _> = bindings
            .iter()
            .map(|(s, b)| (*s, sibling_refs(&b.val, &mut siblings)))
            .collect();

        let groups = group_by_circularity(bindings, &siblings_out_refs);

        // For each group, what other groups does it refer to (by index in `groups`)?
        let groups_out_refs = groups
            .keys()
            .map(|&n| (n, group_refs(n, &groups, &siblings_out_refs)))
            .collect::<HashMap<_, _>>();

        // For each group (index), the number of incoming edges
        let mut groups_n_incoming = vec![0; groups.len()];
        for (_, group_out_refs) in &groups_out_refs {
            for &out_ref in group_out_refs {
                groups_n_incoming[out_ref] += 1;
            }
        }

        let topo_ordered_groups = topological_sort(groups, &groups_out_refs, groups_n_incoming);

        TopologicallyOrderedDependencyGroups(topo_ordered_groups)
    }

    fn into_iter(self) -> impl DoubleEndedIterator<Item = Group<'src>> {
        self.0.into_iter()
    }
}

impl<'src> fmt::Debug for TopologicallyOrderedDependencyGroups<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.0
                .iter()
                .map(|g| {
                    format!("[{}]", g.iter_keys().intersperse(", ").collect::<String>())
                })
                .intersperse("\n ".to_string())
                .collect::<String>()
        )
    }
}

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
                .keys()
                .filter_map(|id| vars.remove(id).map(|p| (*id, p)))
                .collect::<Vec<_>>();
            for (_, binding) in &mut l.bindings {
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
        Expr::Nil(_) | Expr::NumLit(_) | Expr::StrLit(_) | Expr::Bool(_) => (),
    }
}

/// To correctly generate monomorphizations, wrap the type of a recursive
/// variable in an application
fn wrap_vars_types_in_apps<'src>(
    e: &mut Expr<'src>,
    vars: &mut HashMap<&'src str, Poly<'src>>,
    app_args: &[u64],
) {
    let app_args_t = app_args.iter().map(|n| Type::Var(*n)).collect::<Vec<_>>();
    wrap_vars_types_in_apps_(e, vars, &app_args_t)
}

struct Inferrer<'a, 'src: 'a> {
    /// The environment of variables from let-bindings and function-parameters
    var_env: HashMap<&'src str, Vec<Type<'src>>>,
    /// Declarations of external variables
    externs: &'a HashMap<&'src str, ExternDecl<'src>>,
    /// A map of free type variables to their instantiations
    type_var_map: HashMap<u64, Type<'src>>,
    /// Counter for generation of unique type variable ids
    type_var_gen: &'a mut TypeVarGen,
}

impl<'a, 'src: 'a> Inferrer<'a, 'src> {
    fn new(
        externs: &'a HashMap<&'src str, ExternDecl<'src>>,
        type_var_gen: &'a mut TypeVarGen,
    ) -> Self {
        Inferrer {
            var_env: HashMap::new(),
            externs: externs,
            type_var_map: HashMap::new(),
            type_var_gen: type_var_gen,
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
    fn free_type_vars_poly(&self, p: &Poly<'src>) -> HashSet<u64> {
        let mut set = self.free_type_vars(&p.body);
        for i in &p.params {
            set.remove(i);
        }
        set
    }

    /// Returns an iterator of all free type variables that occur in `t`
    fn free_type_vars(&self, t: &Type<'src>) -> HashSet<u64> {
        match *t {
            Type::Var(n) => {
                self.type_var_map
                    .get(&n)
                    .map(|u| {
                        if occurs_in(n, u, &self.type_var_map) {
                            // NOTE: Shouldn't be able to happen if no bugs right?
                            panic!("ICE: in get_type_vars: t occurs in u")
                        } else {
                            self.free_type_vars(u)
                        }
                    })
                    .unwrap_or(HashSet::from_iter(once(n)))
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
    fn free_type_vars_in_context(&self, t: &Type<'src>) -> HashSet<u64> {
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
                let tvs = repeat_call(|| self.type_var_gen.gen_tv())
                    .take(p.params.len())
                    .collect::<Vec<_>>();
                Type::App(Box::new(TypeFunc::Poly((**p).clone())), tvs)
            }
            _ => t.clone(),
        }
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
            (&Var(n), _) if occurs_in(n, b, &self.type_var_map) => {
                panic!("ICE: unify: `{}` occurs in `{}`", n, b);
            }
            (&Var(n), _) => {
                self.type_var_map.insert(n, b.clone());
                Ok(b.clone())
            }
            (_, &Var(_)) => self.unify(b, a),
            (&App(ref f1, ref ts1), &App(ref f2, ref ts2)) => {
                match (&**f1, &**f2) {
                    (&TypeFunc::Poly(ref p), _) => {
                        assert_eq!(p.params.len(), ts1.len());
                        self.type_var_map.extend(
                            zip(&p.params, ts1).map(|(param, t)| {
                                (*param, t.clone())
                            }),
                        );
                        let a2 = subst(&p.body, &mut self.type_var_map);
                        for param in &p.params {
                            self.type_var_map.remove(param);
                        }
                        self.unify(&a2, b)
                    }
                    (_, &TypeFunc::Poly(_)) => self.unify(b, a),
                    (&TypeFunc::Const(c1), &TypeFunc::Const(c2))
                        if c1 == c2 && ts1.len() == ts2.len() => {
                        zip(ts1, ts2)
                            .map(|(t1, t2)| self.unify(t1, t2))
                            .collect::<Result<_, _>>()
                            .map(|us| App(f1.clone(), us))
                    }
                    _ => Err((a.clone(), b.clone())),
                }
            }
            (&Poly(_), _) | (_, &Poly(_)) => {
                println!("unifying polytype: `{}` U `{}`", a, b);
                unimplemented!()
            }
            (_, _) if a == b => Ok(a.clone()),
            _ => Err((a.clone(), b.clone())),
        }
    }

    /// Check that the expected type of a nil expression is unifiable with the nil type
    fn infer_nil(&mut self, nil: &mut Nil<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_NIL).unwrap_or_else(
            |(e, f)| {
                nil.pos.error_exit(TypeMis(&e, &f))
            },
        )
    }

    /// Check that the expected type of a string literal is unifiable with the string type
    fn infer_str_lit(&mut self, lit: &mut StrLit<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_STRING).unwrap_or_else(
            |(e, f)| {
                lit.pos.error_exit(TypeMis(&e, &f))
            },
        )
    }

    /// Check that the expected type of a boolean literal is unifiable with the boolean type
    fn infer_bool(&mut self, b: &mut Bool<'src>, expected_type: &Type<'src>) -> Type<'src> {
        self.unify(expected_type, &TYPE_BOOL).unwrap_or_else(
            |(e, f)| {
                b.pos.error_exit(TypeMis(&e, &f))
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
                    var.ident.pos.error_exit(TypeMisSub {
                        expected: &subst(expected_type, &mut self.type_var_map),
                        found: &ext.typ,
                        sub_expected: &e,
                        sub_found: &f,
                    })
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
                app.arg.pos().error_exit(TypeMisSub {
                    expected: &subst(func_param_type, &mut self.type_var_map),
                    found: &subst(&arg_type, &mut self.type_var_map),

                    sub_expected: &e,
                    sub_found: &f,
                })
            },
        );
        let ret_unification = self.unify(expected_type, func_ret_type).unwrap_or_else(
            |(e, f)| {
                app.pos.error_exit(TypeMisSub {
                    expected: &subst(expected_type, &mut self.type_var_map),
                    found: &subst(func_ret_type, &mut self.type_var_map),
                    sub_expected: &e,
                    sub_found: &f,
                })
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

        let param_type = self.type_var_gen.gen_tv();
        let body_type = self.type_var_gen.gen_tv();
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

    // TODO: Add indirect recursion
    // TODO: Make order-independent
    /// Infer types for global bindings or bindings of a let-form
    /// and push them to the environment.
    fn infer_bindings(&mut self, bindings: &mut HashMap<&'src str, Binding<'src>>) {
        let bindings_owned = replace(bindings, HashMap::new());
        let top_ord = TopologicallyOrderedDependencyGroups::from_flat_set(bindings_owned);
        for mut recursion_group in top_ord.into_iter().rev() {
            self.infer_recursion_group(&mut recursion_group);
            bindings.extend(recursion_group.into_iter())
        }
    }

    fn infer_let<'l>(
        &mut self,
        let_: &'l mut Let<'src>,
        expected_type: &Type<'src>,
    ) -> &'l Type<'src> {
        self.infer_bindings(&mut let_.bindings);
        let_.typ = self.infer_expr(&mut let_.body, expected_type).clone();
        for name in let_.bindings.keys() {
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
        let arbitrary_cons_type =
            Type::new_cons(self.type_var_gen.gen_tv(), self.type_var_gen.gen_tv());
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
            Expr::App(ref mut app) => self.infer_app(app, expected_type).clone(),
            Expr::If(ref mut cond) => self.infer_if(cond, expected_type).clone(),
            Expr::Lambda(ref mut lam) => self.infer_lambda(lam, expected_type).clone(),
            Expr::Let(ref mut l) => self.infer_let(l, expected_type).clone(),
            Expr::TypeAscript(_) => self.infer_type_ascription(expr, expected_type),
            Expr::Cons(ref mut cons) => self.infer_cons(cons, expected_type).clone(),
        }
    }
}

/// If `var` is an instantiation of a polymorphic value and monomorphization
/// does not already exist for this instantiation type, generate a
/// monomorphization and return the monomorphisized definition
fn monomorphize_def_of_inst<'src>(
    var: &Variable<'src>,
    env: &mut ScopeStack<&str, Binding<'src>>,
) -> Option<(Vec<Type<'src>>, Expr<'src>)> {
    if let Type::App(ref f, ref ts) = var.typ {
        assert!(ts.iter().all(|t| t.is_monomorphic()));
        if let TypeFunc::Poly(ref p) = **f {
            // An application of a polytype =>
            //   it's an instantiation to generate monomorphization for
            let b = env.get(var.ident.s).unwrap();
            if !b.mono_insts.contains_key(ts) {
                // The monomorphization does not already exist
                let mut s = zip(&p.params, ts)
                    .map(|(param, t)| (param.clone(), t.clone()))
                    .collect();
                let mut def_mono = b.val.clone();
                subst_expr(&mut def_mono, &mut s);
                return Some((ts.clone(), def_mono));
            }
        }
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
        Expr::Variable(ref var) => {
            if let Some((arg_ts, mut def_mono)) = monomorphize_def_of_inst(var, env) {
                // Insert dummy monomorphization as a tag to show that monomorphization
                // already has been done, but we still need `def_mono` to continue
                // our recursive monomorphization
                {
                    let dummy_expr =
                        Expr::Nil(Nil { pos: SrcPos::new_pos(path::Path::new(""), "", 0) });
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
        Expr::Let(ref mut l) => {
            let mut bindings = replace(&mut l.bindings, HashMap::new());
            monomorphize_defs_of_insts_in_let(&mut bindings, &mut l.body, env);
            l.bindings = bindings;
        }
        Expr::TypeAscript(_) => unreachable!(),
        Expr::Cons(ref mut cons) => {
            monomorphize_defs_of_insts_in_expr(&mut cons.car, env);
            monomorphize_defs_of_insts_in_expr(&mut cons.cdr, env);
        }
        _ => (),
    }
}

/// Monomorphize definitions for monomorphic instantiations of variables in `bindings`
fn monomorphize_defs_of_insts_in_let<'src>(
    bindings: &mut HashMap<&'src str, Binding<'src>>,
    body: &mut Expr<'src>,
    env: &mut ScopeStack<&'src str, Binding<'src>>,
) {
    let bindings2 = replace(bindings, HashMap::new());

    let mut ids = Vec::new();
    let mut monos = HashMap::new();
    let mut local_bindings = HashMap::new();
    for (id, b) in bindings2 {
        ids.push(id);
        if b.typ.is_monomorphic() {
            monos.insert(id, b.val.clone());
        }
        local_bindings.insert(id, b);
    }
    env.push(local_bindings);

    for (_, mut def) in &mut monos {
        monomorphize_defs_of_insts_in_expr(&mut def, env);
    }
    monomorphize_defs_of_insts_in_expr(body, env);

    let mut local_bindings = env.pop().unwrap();
    for id in ids {
        let mut b = local_bindings.remove(id).unwrap();
        if let Some(upd_def) = monos.remove(id) {
            b.val = upd_def;
        }
        bindings.insert(id, b);
    }
}

/// Monomorphize definitions for monomorphic instantiations of variables in `bindings`
fn monomorphize_defs_of_insts<'src>(globals: &mut HashMap<&'src str, Binding<'src>>) {
    let mut dummy_body = Expr::Nil(Nil { pos: SrcPos::new_pos("", 0) });
    monomorphize_defs_of_insts_in_let(globals, &mut dummy_body, &mut ScopeStack::new());
}

pub fn infer_types(module: &mut Module, type_var_generator: &mut TypeVarGen) {
    let mut inferrer = Inferrer::new(&mut module.externs, type_var_generator);

    if let Some(mut main) = module.globals.remove("main") {
        let expected_main_type = Type::new_func(TYPE_NIL.clone(), TYPE_NIL.clone());
        let type_ascribed = Expr::TypeAscript(Box::new(TypeAscript {
            typ: expected_main_type,
            expr: main.val,
            pos: main.pos.clone(),
        }));
        main.val = type_ascribed;
        module.globals.insert("main", main);
    }

    inferrer.infer_bindings(&mut module.globals);

    // Apply all substitutions recursively to get rid of reduntant, indirect type variables
    for (_, binding) in &mut module.globals {
        binding.typ = subst(&binding.typ, &mut inferrer.type_var_map);
        subst_expr(&mut binding.val, &mut inferrer.type_var_map);
    }

    // Map monomorphic instantiations of variables to monomorphization of definitions
    monomorphize_defs_of_insts(&mut module.globals);
}
