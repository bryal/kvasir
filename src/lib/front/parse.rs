// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use self::ParseErr::*;
use super::*;
use super::ast::*;
use super::lex::CST;
use std::collections::{HashMap, BTreeMap, HashSet};
use std::fmt::{self, Display};
use std::iter::once;

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
                .ids()
                .filter_map(|id| if siblings.remove(id) { Some(id) } else { None })
                .collect::<Vec<_>>();
            let refs = l.bindings
                .bindings()
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
        Car(ref c) => sibling_refs(&c.expr, siblings),
        Cdr(ref c) => sibling_refs(&c.expr, siblings),
        TypeAscript(ref a) => sibling_refs(&a.expr, siblings),
        Cast(ref c) => sibling_refs(&c.expr, siblings),
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
        .ids()
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

fn flat_bindings_to_topologically_ordered<'src>(
    bindings: HashMap<&'src str, Binding<'src>>,
) -> TopologicallyOrderedDependencyGroups<'src> {
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

/// Constructors for common parse errors to prevent repetition and spelling mistakes
enum ParseErr {
    /// Something is invalid
    Invalid(&'static str),
    /// Mismatch between two items. Something was expected, but something else was found
    Mismatch(&'static str, &'static str),
    /// Mismatch in the amount of parameters given. Some amount was expected, another was given
    ArityMis(usize, usize),
    /// Something was expected (and not found)
    Expected(&'static str),
}
impl Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Invalid(s) => write!(f, "Invalid {}", s),
            Mismatch(expected, found) => write!(f, "Expected {}, found {}", expected, found),
            ArityMis(expected, found) => {
                write!(f, "Arity mismatch. Expected {}, found {}", expected, found)
            }
            Expected(e) => write!(f, "Expected {}", e),
        }
    }
}

/// A binding pattern
///
/// Patterns are used in variable bindings as a sort of syntax sugar
enum Pattern<'src> {
    /// Just an identifier
    Var(Ident<'src>),
    /// A function-binding pattern. E.g. `(inc x)`
    Func(Ident<'src>, (Vec<Ident<'src>>, SrcPos<'src>)),
}

struct Parser<'tvg> {
    /// Counter for generation of unique type variable ids
    type_var_gen: &'tvg mut TypeVarGen,
}

impl<'tvg> Parser<'tvg> {
    fn new(type_var_gen: &'tvg mut TypeVarGen) -> Self {
        Parser { type_var_gen }
    }

    fn gen_tvar<'src>(&mut self) -> TVar<'src> {
        TVar {
            id: self.type_var_gen.gen(),
            constrs: BTreeSet::new(),
            explicit: None,
        }
    }

    fn gen_type_var<'src>(&mut self) -> Type<'src> {
        Type::Var(self.gen_tvar())
    }

    /// Parse a syntax tree as a tuple of `n` syntax trees
    fn parse_tuple<'src, 'c>(&mut self, cst: &'c CST<'src>, n: usize) -> &'c [CST<'src>] {
        match *cst {
            CST::SExpr(ref csts, _) if csts.len() == n => csts,
            CST::SExpr(ref csts, ref pos) => pos.error_exit(ArityMis(n, csts.len())),
            _ => cst.pos().error_exit(Expected("s-expression")),
        }
    }

    fn parse_pair<'src, 'c>(&mut self, cst: &'c CST<'src>) -> (&'c CST<'src>, &'c CST<'src>) {
        let pair = self.parse_tuple(cst, 2);
        (&pair[0], &pair[1])
    }

    fn parse_constraint<'src>(&mut self, cst: &CST<'src>) -> &'src str {
        match *cst {
            CST::Ident("Num", _) => "Num",
            CST::Ident(s, ref pos) => pos.error_exit(format!("Undefined constraint {}", s)),
            _ => cst.pos().error_exit("Invalid constraint"),
        }
    }

    /// Parse a specification of constraints for a type variable
    ///
    /// E.g. `(: t Num)`
    fn parse_constraints_spec<'src>(&mut self, csts: &[CST<'src>]) -> TVar<'src> {
        match csts[0] {
            CST::Ident(s, _) if s.starts_with(char::is_lowercase) => {
                TVar {
                    id: self.type_var_gen.gen(),
                    constrs: csts[1..]
                        .iter()
                        .map(|cst| self.parse_constraint(cst))
                        .collect::<BTreeSet<&'src str>>(),
                    explicit: Some(s),
                }
            }
            ref cst => {
                cst.pos().error_exit(
                    "Invalid type variable. Type variable must begin with a lower case letter",
                )
            }
        }
    }

    /// Parse a syntax tree as a `Type`, keeping track och implicitly defined type variables
    fn parse_type_with_tvars<'src>(
        &mut self,
        tvars: &mut HashMap<&'src str, (TVar<'src>, SrcPos<'src>)>,
        tree: &CST<'src>,
    ) -> Type<'src> {
        match *tree {
            // Type application, e.g. `(Vec Int32)`; or type variable with constraints,
            // e.g. `(: t Num)`
            CST::SExpr(ref app, ref pos) if !app.is_empty() => {
                match app[0] {
                    CST::Ident(":", _) if app.len() > 2 => {
                        let tv = self.parse_constraints_spec(&app[1..]);
                        let name = tv.explicit.unwrap();
                        if tvars.contains_key(name) {
                            let first_pos = &tvars.get(name).unwrap().1;
                            pos.error("Type variable has already been defined in this scope");
                            first_pos.note(
                                "A type variable is implicitly defined the first time it is used \
                                 in a scope.\nTry removing the constraints of this instance of \
                                 the type variable, \nand add them to the first instance instead.\n\
                                 The first instance of the type variable is here:",
                            );
                            exit()
                        } else {
                            tvars.insert(tv.explicit.unwrap(), (tv.clone(), pos.clone()));
                            Type::Var(tv)
                        }
                    }
                    CST::Ident(":", _) => {
                        pos.error_exit(
                            "Constraint specification requires at least two arguments: \
                             the type variable to constrain, and one/multiple constraint(s)",
                        )
                    }
                    CST::Ident("->", _) if app.len() < 3 => {
                        pos.error_exit(
                            "Function type constructor requires at least two arguments: \
                             one/multiple input type(s) and an output type",
                        )
                    }
                    CST::Ident("->", _) if app.len() == 3 => {
                        Type::new_func(
                            self.parse_type_with_tvars(tvars, &app[1]),
                            self.parse_type_with_tvars(tvars, &app[2]),
                        )
                    }
                    CST::Ident("->", _) => {
                        let last_fn = Type::new_func(
                            self.parse_type_with_tvars(tvars, &app[app.len() - 2]),
                            self.parse_type_with_tvars(tvars, &app[app.len() - 1]),
                        );
                        app[1..app.len() - 2].iter().rev().fold(last_fn, |acc, t| {
                            Type::new_func(self.parse_type_with_tvars(tvars, t), acc)
                        })
                    }
                    CST::Ident("Cons", _) if app.len() == 3 => {
                        Type::new_cons(
                            self.parse_type_with_tvars(tvars, &app[1]),
                            self.parse_type_with_tvars(tvars, &app[2]),
                        )
                    }
                    CST::Ident("Cons", _) => pos.error_exit(ArityMis(2, app.len() - 1)),
                    CST::Ident("Ptr", _) if app.len() == 2 => {
                        Type::new_ptr(self.parse_type_with_tvars(tvars, &app[1]))
                    }
                    CST::Ident("Ptr", _) => pos.error_exit(ArityMis(1, app.len() - 1)),
                    CST::Ident(c, ref c_pos) => {
                        c_pos.error_exit(format!("Undefined type constructor `{}`", c))
                    }
                    _ => app[0].pos().error_exit(Invalid("type constructor")),
                }
            }
            CST::SExpr(_, ref pos) => pos.error_exit("Empty type application"),
            CST::Ident("_", _) => self.gen_type_var(),
            CST::Ident("Nil", _) => TYPE_NIL.clone(),
            // The type identifier starts with a lowercase letter => Is a type variable
            CST::Ident(s, ref pos) if s.starts_with(char::is_lowercase) => {
                let tv = tvars
                    .entry(s)
                    .or_insert((
                        TVar {
                            id: self.type_var_gen.gen(),
                            constrs: BTreeSet::new(),
                            explicit: Some(s),
                        },
                        pos.clone(),
                    ))
                    .0
                    .clone();
                Type::Var(tv)
            }
            // Doesn't start with lowercase => Is a type constant e.g. Int32
            CST::Ident(s, ref pos) => Type::Const(s, Some(pos.clone())),
            CST::Num(_, ref pos) => pos.error_exit(Mismatch("type", "numeric literal")),
            CST::Str(_, ref pos) => pos.error_exit(Mismatch("type", "string literal")),
        }
    }

    /// Parse a syntax tree as a `Type`
    fn parse_type<'src>(&mut self, tree: &CST<'src>) -> Type<'src> {
        self.parse_type_with_tvars(&mut HashMap::new(), tree)
    }

    /// Parse a `CST` as an `Ident` (identifier)
    fn parse_ident<'src>(&mut self, cst: &CST<'src>) -> Ident<'src> {
        match *cst {
            CST::Ident(ident, ref pos) => Ident::new(ident, pos.clone()),
            _ => cst.pos().error_exit(Invalid("identifier")),
        }
    }

    /// Parse a syntax tree as a Pattern
    fn parse_pattern<'src>(&mut self, cst: &CST<'src>) -> Pattern<'src> {
        match *cst {
            CST::Ident(ident, ref pos) => Pattern::Var(Ident::new(ident, pos.clone())),
            CST::SExpr(ref app, _) if app.len() > 1 => {
                let f_id = self.parse_ident(&app[0]);
                let params_ids = app[1..]
                    .iter()
                    .map(|a| self.parse_ident(a))
                    .collect::<Vec<_>>();
                let params_pos = params_ids[0].pos.to(&params_ids.last().unwrap().pos);
                Pattern::Func(f_id, (params_ids, params_pos))
            }
            CST::SExpr(ref app, ref pos) if app.len() == 1 => {
                pos.error_exit("Function binding pattern requires at least one parameter")
            }
            _ => cst.pos().error_exit(Invalid("pattern")),
        }
    }

    fn new_multary_app<'src>(
        &mut self,
        func: Expr<'src>,
        mut args: Vec<Expr<'src>>,
        pos: SrcPos<'src>,
    ) -> App<'src> {
        let last = args.pop().unwrap_or_else(|| {
            pos.error_exit(
                "Empty argument list. Function applications can't be nullary",
            )
        });
        let apps = args.into_iter().fold(func, |f, arg| {
            Expr::App(Box::new(App {
                func: f,
                arg: arg,
                typ: self.gen_type_var(),
                pos: pos.clone(),
            }))
        });
        App {
            func: apps,
            arg: last,
            typ: self.gen_type_var(),
            pos: pos,
        }
    }

    /// Parse a first `CST` and some following `CST`s as a procedure and some arguments,
    /// i.e. a function application
    fn parse_app<'src>(
        &mut self,
        func_cst: &CST<'src>,
        args_csts: &[CST<'src>],
        pos: SrcPos<'src>,
    ) -> App<'src> {
        let func = self.parse_expr(func_cst);
        let args = args_csts.iter().map(|a| self.parse_expr(a)).collect();
        self.new_multary_app(func, args, pos)
    }

    /// Parse a list of `CST`s as parts of an `If` conditional
    fn parse_if<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> If<'src> {
        if csts.len() != 3 {
            pos.error_exit(ArityMis(3, csts.len()))
        } else {
            If {
                predicate: self.parse_expr(&csts[0]),
                consequent: self.parse_expr(&csts[1]),
                alternative: self.parse_expr(&csts[2]),
                typ: self.gen_type_var(),
                pos: pos,
            }
        }
    }

    /// Parse the `else` clause of a `cond`
    fn parse_else_clause<'src>(&mut self, cst: &CST<'src>) -> Expr<'src> {
        let (pred, conseq) = self.parse_pair(cst);
        if pred.ident() == Some("else") {
            self.parse_expr(conseq)
        } else {
            cst.pos().error_exit("Expected `else`")
        }
    }

    /// Parse a clause of a `cond`
    fn parse_cond_clause<'src>(&mut self, cst: &CST<'src>) -> (Expr<'src>, Expr<'src>) {
        let (pred_cst, conseq_cst) = self.parse_pair(cst);
        (self.parse_expr(pred_cst), self.parse_expr(conseq_cst))
    }

    /// Parse a sequence of token trees as the clauses of a `cond` special form
    ///
    /// Translate to nested `If`s
    fn parse_cond<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Expr<'src> {
        if let Some((last, init)) = csts.split_last() {
            let else_val = self.parse_else_clause(last);
            init.iter().rev().fold(else_val, |alternative, c| {
                let (predicate, consequent) = self.parse_cond_clause(c);
                Expr::If(box If {
                    predicate,
                    consequent,
                    alternative,
                    pos: c.pos().clone(),
                    typ: self.gen_type_var(),
                })
            })
        } else {
            pos.error_exit(
                "No clauses in `cond`.\n\
                            Must contain at lease one clause, \
                            where the last clause is the `else` clause.",
            )
        }
    }

    fn new_multary_lambda<'src>(
        &mut self,
        mut params: Vec<(Ident<'src>, Type<'src>)>,
        params_pos: &SrcPos<'src>,
        body: Expr<'src>,
        pos: &SrcPos<'src>,
    ) -> Lambda<'src> {
        let last_param = params.pop().unwrap_or_else(|| {
            params_pos.error_exit(
                "Empty parameter list. Functions can't be \
             nullary, consider defining a constant instead",
            )
        });
        let innermost = Lambda {
            param_ident: last_param.0,
            param_type: last_param.1,
            body: body,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        };

        params.into_iter().rev().fold(innermost, |inner, param| {
            Lambda {
                param_ident: param.0,
                param_type: param.1,
                body: Expr::Lambda(Box::new(inner)),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            }
        })
    }

    /// Parse a list of `CST`s as the parts of a `Lambda`
    fn parse_lambda<'src>(&mut self, csts: &[CST<'src>], pos: &SrcPos<'src>) -> Lambda<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }
        match csts[0] {
            CST::SExpr(ref params_csts, ref params_pos) => {
                let params = params_csts
                    .iter()
                    .map(|param_cst| {
                        (self.parse_ident(param_cst), self.gen_type_var())
                    })
                    .collect();
                let body = self.parse_expr(&csts[1]);
                self.new_multary_lambda(params, params_pos, body, pos)
            }
            _ => csts[0].pos().error_exit(Expected("parameter list")),
        }
    }

    /// Parse a list of syntax trees as a variable binding
    ///
    /// A binding consists of a pattern and a definition.
    /// Used for parsing both the contents of a `define` special form, and the bindings of a
    /// `let` special form.
    ///
    /// # Examples
    /// Following are some example bindings
    /// ```
    /// (define num 1)
    /// (define id (lambda (x) x)) ; { These two are equivalent.
    /// (define (id2        x) x)  ;   Just syntax sugar }
    /// (let ((num 1)
    ///       (id (lambda (x) x))
    ///       ((id2        x) x))
    ///   ...)
    /// ```
    fn parse_binding<'src>(&mut self, csts: &[CST<'src>], pos: &SrcPos<'src>) -> Binding<'src> {
        if csts.len() == 2 {
            match self.parse_pattern(&csts[0]) {
                Pattern::Var(ident) => Binding {
                    ident: ident,
                    typ: self.gen_type_var(),
                    val: self.parse_expr(&csts[1]),
                    mono_insts: HashMap::new(),
                    pos: pos.clone(),
                },
                Pattern::Func(f_id, (params_ids, params_pos)) => {
                    let params = params_ids
                        .into_iter()
                        .map(|id| (id, self.gen_type_var()))
                        .collect::<Vec<_>>();
                    let body = self.parse_expr(&csts[1]);
                    Binding {
                        ident: f_id,
                        typ: self.gen_type_var(),
                        val: Expr::Lambda(Box::new(
                            self.new_multary_lambda(params, &params_pos, body, pos),
                        )),
                        mono_insts: HashMap::new(),
                        pos: pos.clone(),
                    }
                }
            }

        } else {
            pos.error_exit(Expected("pair of binding pattern and definition"))
        }
    }

    fn parse_bindings_to_flat_map<'src>(
        &mut self,
        defs: &[(&[CST<'src>], &SrcPos<'src>)],
    ) -> HashMap<&'src str, Binding<'src>> {
        let mut bindings = HashMap::new();
        for &(def_csts, pos) in defs {
            let binding = self.parse_binding(def_csts, pos);
            let (new_id, new_pos) = (binding.ident.s, binding.pos.clone());
            if let Some(prev_binding) = bindings.insert(new_id, binding) {
                new_pos.error_exit(format!(
                    "Conflicting definition of variable `{}`\n\
                             Previous definition here `{:?}`",
                    new_id,
                    prev_binding.pos
                ))
            }
        }
        bindings
    }

    fn parse_bindings<'src>(
        &mut self,
        defs: &[(&[CST<'src>], &SrcPos<'src>)],
    ) -> TopologicallyOrderedDependencyGroups<'src> {
        let bindings = self.parse_bindings_to_flat_map(defs);
        flat_bindings_to_topologically_ordered(bindings)
    }

    fn parse_let_bindings<'src>(
        &mut self,
        csts: &[CST<'src>],
    ) -> TopologicallyOrderedDependencyGroups<'src> {
        let mut bindings_csts = Vec::<(&[_], _)>::new();
        for cst in csts {
            match *cst {
                CST::SExpr(ref binding_pair, ref pos) => bindings_csts.push((binding_pair, pos)),
                ref c => c.pos().error_exit(Expected("variable binding")),
            }
        }
        self.parse_bindings(&bindings_csts)
    }

    /// Parse a `let` special form and return as an invocation of a lambda
    fn parse_let<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Let<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }

        let body = self.parse_expr(&csts[1]);

        match csts[0] {
            CST::SExpr(ref bindings_csts, _) => Let {
                bindings: self.parse_let_bindings(bindings_csts),
                body: body,
                typ: self.gen_type_var(),
                pos: pos.clone(),
            },
            ref c => c.pos().error_exit(Expected("list of variable bindings")),
        }
    }

    /// Parse a list of `CST`s as a `TypeAscript`
    fn parse_type_ascript<'src>(
        &mut self,
        csts: &[CST<'src>],
        pos: SrcPos<'src>,
    ) -> TypeAscript<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }
        TypeAscript {
            typ: self.parse_type(&csts[1]),
            expr: self.parse_expr(&csts[0]),
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as a `Cons` pair
    fn parse_cons<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Cons<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }
        Cons {
            typ: self.gen_type_var(),
            car: self.parse_expr(&csts[0]),
            cdr: self.parse_expr(&csts[1]),
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as a `car` operation
    fn parse_car<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Car<'src> {
        if csts.len() != 1 {
            pos.error_exit(ArityMis(1, csts.len()))
        }
        Car {
            typ: self.gen_type_var(),
            expr: self.parse_expr(&csts[0]),
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as a `cdr` operation
    fn parse_cdr<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Cdr<'src> {
        if csts.len() != 1 {
            pos.error_exit(ArityMis(1, csts.len()))
        }
        Cdr {
            typ: self.gen_type_var(),
            expr: self.parse_expr(&csts[0]),
            pos: pos,
        }
    }

    /// Parse a type cast
    ///
    /// `(cast VAL TYPE)`, e.g. `(cast (: 1 Int32) Int64)`
    fn parse_cast<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Cast<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }
        Cast {
            expr: self.parse_expr(&csts[0]),
            typ: self.parse_type(&csts[1]),
            pos: pos,
        }
    }

    /// Apply either the `>>` or `>>=` action
    fn app_action<'src>(&mut self, f: &'static str, a: Expr<'src>, b: Expr<'src>) -> Expr<'src> {
        let f_var = Expr::Variable(Variable {
            ident: Ident {
                s: f,
                pos: SrcPos::new_dummy(),
            },
            typ: self.gen_type_var(),
        });
        Expr::App(box self.new_multary_app(
            f_var,
            vec![a, b],
            SrcPos::new_dummy(),
        ))
    }

    /// Parse a syntax tree as an io "statement"
    ///
    /// Either an IO expression which translates to `>>`,
    /// or a `<-` assignment which translates to `>>=`.
    fn parse_io_statement<'src>(&mut self, cst: &CST<'src>, next: Expr<'src>) -> Expr<'src> {
        if let Some(v) = cst.application_of("<-") {
            if v.len() == 2 {
                if let Some(id) = v[0].ident() {
                    let first_expr = self.parse_expr(&v[1]);
                    let next_lam = Expr::Lambda(box Lambda {
                        param_ident: Ident {
                            s: id,
                            pos: v[0].pos().clone(),
                        },
                        param_type: self.gen_type_var(),
                        body: next,
                        typ: self.gen_type_var(),
                        pos: SrcPos::new_dummy(),
                    });
                    self.app_action(">>=", first_expr, next_lam)
                } else {
                    v[0].pos().error_exit(Expected("identifier"))
                }
            } else {
                cst.pos().error_exit(ArityMis(2, v.len()))
            }
        } else {
            let first = self.parse_expr(cst);
            self.app_action(">>", first, next)
        }
    }

    /// Parse a sequence of token trees as a pipe (sequence) of io "statements"
    ///
    /// Translate to applications of `>>` and `>>=`. These functions must be defined
    /// in source to not invoke a compiler error.
    fn parse_io_pipe<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Expr<'src> {
        if let Some((last, init)) = csts.split_last() {
            let ret = self.parse_expr(last);
            init.iter().rev().fold(ret, |next, cst| {
                self.parse_io_statement(cst, next)
            })
        } else {
            pos.error_exit(
                "No statements in `io-pipe`.\nMust contain at lease one statement.",
            )
        }
    }

    /// Parse a `CST` as an `Expr`
    fn parse_expr<'src>(&mut self, cst: &CST<'src>) -> Expr<'src> {
        match *cst {
            CST::SExpr(ref sexpr, ref pos) => {
                if let Some((head, tail)) = sexpr.split_first() {
                    match *head {
                        CST::Ident("if", _) => Expr::If(Box::new(self.parse_if(tail, pos.clone()))),
                        CST::Ident("lambda", _) => Expr::Lambda(
                            Box::new(self.parse_lambda(tail, pos)),
                        ),
                        CST::Ident("let", _) => Expr::Let(
                            Box::new(self.parse_let(tail, pos.clone())),
                        ),
                        CST::Ident(":", _) => {
                            Expr::TypeAscript(Box::new(self.parse_type_ascript(tail, pos.clone())))
                        }
                        CST::Ident("cons", _) => Expr::Cons(
                            Box::new(self.parse_cons(tail, pos.clone())),
                        ),
                        CST::Ident("car", _) => Expr::Car(
                            Box::new(self.parse_car(tail, pos.clone())),
                        ),
                        CST::Ident("cdr", _) => Expr::Cdr(
                            Box::new(self.parse_cdr(tail, pos.clone())),
                        ),
                        CST::Ident("cast", _) => Expr::Cast(
                            Box::new(self.parse_cast(tail, pos.clone())),
                        ),

                        // "Macros"
                        CST::Ident("cond", _) => self.parse_cond(tail, pos.clone()),
                        CST::Ident("io-pipe", _) => self.parse_io_pipe(tail, pos.clone()),

                        _ => Expr::App(Box::new(self.parse_app(&sexpr[0], tail, pos.clone()))),
                    }
                } else {
                    Expr::Nil(Nil { pos: pos.clone() })
                }
            }
            CST::Ident("nil", ref pos) => Expr::Nil(Nil { pos: pos.clone() }),
            CST::Ident("true", ref pos) => {
                Expr::Bool(Bool {
                    val: true,
                    pos: pos.clone(),
                })
            }
            CST::Ident("false", ref pos) => {
                Expr::Bool(Bool {
                    val: false,
                    pos: pos.clone(),
                })
            }
            CST::Ident(ident, ref pos) => {
                Expr::Variable(Variable {
                    ident: Ident::new(ident, pos.clone()),
                    typ: self.gen_type_var(),
                })
            }
            CST::Num(num, ref pos) => {
                Expr::NumLit(NumLit {
                    lit: num,
                    typ: self.gen_type_var(),
                    pos: pos.clone(),
                })
            }
            CST::Str(ref s, ref pos) => {
                Expr::StrLit(StrLit {
                    lit: s.clone(),
                    typ: self.gen_type_var(),
                    pos: pos.clone(),
                })
            }
        }
    }

    /// Separate `csts` into token trees for globals end externs
    fn group_top_level_csts<'c, 'src>(
        &mut self,
        csts: &'c [CST<'src>],
    ) -> (Vec<(&'c [CST<'src>], &'c SrcPos<'src>)>, Vec<(&'c [CST<'src>], &'c SrcPos<'src>)>) {
        let (mut globals, mut externs) = (Vec::new(), Vec::new());
        for cst in csts {
            let pos = cst.pos();
            match *cst {
                CST::SExpr(ref sexpr, _) if !sexpr.is_empty() => {
                    match sexpr[0] {
                        CST::Ident("define", _) => {
                            globals.push((&sexpr[1..], pos));
                            continue;
                        }
                        CST::Ident("extern", _) => {
                            externs.push((&sexpr[1..], pos));
                            continue;
                        }
                        _ => (),
                    }
                }
                _ => (),
            }
            pos.error_exit("Unexpected token-tree at top-level")
        }
        (globals, externs)
    }

    /// Parse a list of `CST`s as an external variable declaration
    fn parse_extern<'src>(&mut self, csts: &[CST<'src>], pos: &SrcPos<'src>) -> ExternDecl<'src> {
        if csts.len() != 2 {
            pos.error_exit(
                "Invalid external variable declaration. Expected identifier and type",
            )
        } else {
            match csts[0] {
                CST::Ident(name, ref id_pos) => {
                    // Type must be monomorphic canonical
                    let typ = self.parse_type(&csts[1]).canonicalize();
                    if !typ.is_monomorphic() {
                        csts[1].pos().error_exit(
                            "Type of external variable must be fully specified",
                        )
                    }
                    ExternDecl {
                        ident: Ident::new(name, id_pos.clone()),
                        typ: typ,
                        pos: pos.clone(),
                    }
                }
                _ => csts[0].pos().error_exit(Expected("identifier")),
            }
        }
    }

    fn parse_externs<'src>(
        &mut self,
        decls_csts: &[(&[CST<'src>], &SrcPos<'src>)],
    ) -> BTreeMap<&'src str, ExternDecl<'src>> {
        let mut externs = BTreeMap::new();
        for &(decl_csts, pos) in decls_csts {
            let ext = self.parse_extern(decl_csts, pos);
            if let Some(ext) = externs.insert(ext.ident.s, ext) {
                ext.pos.error_exit(format!(
                    "Duplicate declaration of external variable `{}`",
                    ext.ident.s
                ))
            }
        }
        externs
    }

    /// Parse a list of `CST`s as the items of a `Module`
    fn parse_module<'src>(&mut self, csts: &[CST<'src>]) -> Module<'src> {
        // Store globals in a Vec as order matters atm, but disallow
        // multiple definitions. Use a set to keep track of defined globals
        let (globals_csts, externs_csts) = self.group_top_level_csts(csts);
        let globals = self.parse_bindings(&globals_csts);
        let externs = self.parse_externs(&externs_csts);
        Module { globals, externs }
    }
}

pub fn parse<'src>(csts: &[CST<'src>], type_var_generator: &mut TypeVarGen) -> Module<'src> {
    let mut parser = Parser::new(type_var_generator);
    parser.parse_module(csts)
}
