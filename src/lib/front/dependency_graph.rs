//! Functions related to working with dependency graphs
//!
//! For example, given a set of maybe recursive functions, you want
//! to order them such that the type signatures can be determined completely.
//! If you put mutually recursive functions together in groups, these groups
//! can then be placed in a DAG of dependency relations. This DAG can then be
//! topologically ordered, and we can infer the types as well as possible.

use std::iter::once;
use std::collections::{BTreeMap, BTreeSet};
use super::ast::*;

/// Returns a set of all siblings being referred to in this expression
fn sibling_refs<'src>(e: &Expr<'src>, siblings: &mut BTreeSet<&'src str>) -> BTreeSet<&'src str> {
    use self::Expr::*;
    match *e {
        Variable(ref v) => {
            if siblings.contains(v.ident.s) {
                once(v.ident.s).collect()
            } else {
                BTreeSet::new()
            }
        }
        App(ref app) => [&app.func, &app.arg]
            .iter()
            .flat_map(|e2| sibling_refs(e2, siblings))
            .collect(),
        If(ref cond) => [&cond.predicate, &cond.consequent, &cond.alternative]
            .iter()
            .flat_map(|e2| sibling_refs(e2, siblings))
            .collect(),
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
        Cons(ref c) => [&c.car, &c.cdr]
            .iter()
            .flat_map(|e2| sibling_refs(e2, siblings))
            .collect(),
        Car(ref c) => sibling_refs(&c.expr, siblings),
        Cdr(ref c) => sibling_refs(&c.expr, siblings),
        TypeAscript(ref a) => sibling_refs(&a.expr, siblings),
        Cast(ref c) => sibling_refs(&c.expr, siblings),
        OfVariant(ref x) => sibling_refs(&x.expr, siblings),
        AsVariant(ref x) => sibling_refs(&x.expr, siblings),
        Nil(_) | NumLit(_) | StrLit(_) | Bool(_) => BTreeSet::new(),
    }
}

fn circular_def_members_<'src>(
    start: &'src str,
    current: &'src str,
    siblings_out_refs: &BTreeMap<&str, BTreeSet<&'src str>>,
    visited: &mut BTreeSet<&'src str>,
) -> BTreeSet<&'src str> {
    if current == start && visited.contains(current) {
        once(current).collect()
    } else if visited.contains(current) {
        BTreeSet::new()
    } else {
        visited.insert(current);
        let mut members = BTreeSet::new();
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
    siblings_out_refs: &BTreeMap<&str, BTreeSet<&'src str>>,
) -> BTreeSet<&'src str> {
    let mut visited = BTreeSet::new();
    circular_def_members_(s, s, siblings_out_refs, &mut visited)
}

/// Group sets of circularly referencing bindings together, to make
/// the inter-group relation acyclic.
fn group_by_circularity<'src>(
    mut bindings: BTreeMap<&'src str, Binding<'src>>,
    siblings_out_refs: &BTreeMap<&'src str, BTreeSet<&'src str>>,
) -> BTreeMap<usize, Group<'src>> {
    let mut n = 0;
    let mut groups = BTreeMap::<usize, Group>::new();
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
    groups: &BTreeMap<usize, Group>,
    siblings_out_refs: &BTreeMap<&str, BTreeSet<&str>>,
) -> BTreeSet<usize> {
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
    mut groups: BTreeMap<usize, Group<'src>>,
    groups_out_refs: &BTreeMap<usize, BTreeSet<usize>>,
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

pub fn flat_bindings_to_topologically_ordered<'src>(
    bindings: BTreeMap<&'src str, Binding<'src>>,
) -> TopologicallyOrderedDependencyGroups<'src> {
    let mut siblings: BTreeSet<_> = bindings.keys().cloned().collect();
    let siblings_out_refs: BTreeMap<_, _> = bindings
        .iter()
        .map(|(s, b)| (*s, sibling_refs(&b.val, &mut siblings)))
        .collect();

    let groups = group_by_circularity(bindings, &siblings_out_refs);

    // For each group, what other groups does it refer to (by index in `groups`)?
    let groups_out_refs = groups
        .keys()
        .map(|&n| (n, group_refs(n, &groups, &siblings_out_refs)))
        .collect::<BTreeMap<_, _>>();

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
