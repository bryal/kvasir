use lib::{map_of, set_of};
use super::SrcPos;
use super::cst::*;
use std::collections::{BTreeMap, BTreeSet};

fn match_multi<'s>(
    ps: &[Pattern<'s>],
    cs: &[Cst<'s>],
    pos: &SrcPos<'s>,
) -> Option<BTreeMap<&'s str, Cst<'s>>> {
    let mut binding_vs = ps.iter()
        .flat_map(|p| p.idents())
        .map(|id| (id, Vec::new()))
        .collect::<BTreeMap<&str, Vec<Cst<'s>>>>();
    if cs.len() % ps.len() != 0 {
        None
    } else {
        let mut i = 0;
        while i < cs.len() {
            for p in ps {
                for (k, v) in p.match_(&cs[i])? {
                    binding_vs
                        .get_mut(k)
                        .expect("ICE: Key not in binding_vs in macros::match_multi")
                        .push(v);
                }
                i += 1;
            }
        }
        let bindings = binding_vs
            .into_iter()
            .map(|(k, vs)| (k, Cst::Sexpr(vs, pos.clone())))
            .collect();
        Some(bindings)
    }
}

#[derive(Debug)]
pub enum Pattern<'s> {
    Lit(&'s str),
    Ident(&'s str),
    Multi(Vec<Pattern<'s>>),
    Sexpr(Vec<Pattern<'s>>),
}

impl<'s> Pattern<'s> {
    fn is_multi(&self) -> bool {
        match *self {
            Pattern::Multi(_) => true,
            _ => false,
        }
    }

    fn idents(&self) -> BTreeSet<&'s str> {
        match *self {
            Pattern::Lit(_) => BTreeSet::new(),
            Pattern::Ident(id) => set_of(id),
            Pattern::Multi(ref ps) | Pattern::Sexpr(ref ps) => {
                ps.iter().flat_map(|p| p.idents()).collect()
            }
        }
    }

    fn match_(&self, cst: &Cst<'s>) -> Option<BTreeMap<&'s str, Cst<'s>>> {
        match *self {
            Pattern::Lit(id1) => match *cst {
                Cst::Ident(id2, _) if id1 == id2 => Some(BTreeMap::new()),
                _ => None,
            },
            Pattern::Ident(id) => Some(map_of(id, cst.clone())),
            Pattern::Multi(_) => None,
            Pattern::Sexpr(ref ps) => if let Cst::Sexpr(ref cs, ref pos) = *cst {
                if ps.iter().filter(|p| p.is_multi()).count() <= 1 {
                    let mut cs_i = 0;
                    let mut bindings = BTreeMap::new();
                    for (i, p) in ps.iter().enumerate() {
                        if cs_i > cs.len() {
                            return None;
                        } else if let Pattern::Multi(ref multi_ps) = *p {
                            let n = (cs.len() - cs_i) - (ps.len() - 1 - i);
                            let multi_cs = &cs[cs_i..cs_i + n];
                            bindings.extend(match_multi(multi_ps, multi_cs, pos)?);
                            cs_i += n;
                        } else if cs_i == cs.len() {
                            return None;
                        } else {
                            bindings.extend(p.match_(&cs[cs_i])?);
                            cs_i += 1;
                        }
                    }
                    if cs_i == cs.len() {
                        Some(bindings)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            },
        }
    }
}

pub struct Case<'s> {
    pub pattern: Pattern<'s>,
    pub bodies: Vec<Cst<'s>>,
}

pub struct Macro<'s> {
    pub name: &'s str,
    pub cases: Vec<Case<'s>>,
}

impl<'s> Macro<'s> {
    fn apply(&self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> Vec<Cst<'s>> {
        let args = Cst::Sexpr(csts.to_vec(), pos.clone());
        let (bindings, bodies) = self.cases
            .iter()
            .filter_map(|case| {
                case.pattern
                    .match_(&args)
                    .map(|bindings| (bindings, &case.bodies))
            })
            .next()
            .unwrap_or_else(|| pos.error_exit("No macro pattern matched token trees"));
        bodies
            .iter()
            .flat_map(|body| subst(body, &bindings))
            .collect()
    }
}

fn subst<'s>(cst: &Cst<'s>, s: &BTreeMap<&'s str, Cst<'s>>) -> Vec<Cst<'s>> {
    match *cst {
        Cst::Ident(id, _) if s.contains_key(id) => vec![s[id].clone()],
        Cst::Sexpr(ref cs, ref pos) => {
            if let Some(&Cst::Ident("...", _)) = cs.first() {
                cs[1..]
                    .iter()
                    .flat_map(|c| {
                        subst(c, s).into_iter().flat_map(|c2| match c2 {
                            Cst::Sexpr(ref cs2, _) => cs2.clone(),
                            _ => pos.error_exit("Can't flatten non-list"),
                        })
                    })
                    .collect()
            } else {
                vec![
                    Cst::Sexpr(cs.iter().flat_map(|c| subst(c, s)).collect(), pos.clone()),
                ]
            }
        }
        _ => vec![cst.clone()],
    }
}

pub fn expand_macros<'s>(cst: &Cst<'s>, macros: &BTreeMap<&'s str, Macro<'s>>) -> Vec<Cst<'s>> {
    match *cst {
        Cst::Sexpr(ref cs, ref pos) if !cs.is_empty() => match cs[0] {
            Cst::Ident(id, _) if macros.contains_key(id) => macros[id]
                .apply(&cs[1..], pos)
                .iter()
                .flat_map(|c| expand_macros(&c, macros))
                .collect(),
            _ => vec![
                Cst::Sexpr(
                    cs.iter().flat_map(|c| expand_macros(c, macros)).collect(),
                    pos.clone(),
                ),
            ],
        },
        _ => vec![cst.clone()],
    }
}
