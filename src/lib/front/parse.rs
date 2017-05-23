// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use self::ParseErr::*;
use super::SrcPos;
use super::ast::*;
use super::lex::CST;
use std::collections::HashMap;
use std::fmt::{self, Display};

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

/// Parse a `CST` as a `Type`
pub fn parse_type<'src>(tree: &CST<'src>) -> Type<'src> {
    match *tree {
        // Type construction. E.g. `(Vec Int32)`
        CST::SExpr(ref construct, _) if !construct.is_empty() => {
            match construct[0] {
                CST::Ident(constructor, _) => {
                    Type::App(constructor, construct[1..].iter().map(parse_type).collect())
                }
                _ => construct[0].pos().error_exit(Invalid("type constructor")),
            }
        }
        CST::SExpr(_, ref pos) => pos.error_exit("Empty type construction"),
        CST::Ident("_", _) => Type::Uninferred,
        CST::Ident("Nil", _) => TYPE_NIL.clone(),
        CST::Ident(basic, _) => Type::Const(basic),
        CST::Num(_, ref pos) => pos.error_exit(Mismatch("type", "numeric literal")),
        CST::Str(_, ref pos) => pos.error_exit(Mismatch("type", "string literal")),
    }
}

/// Parse a `CST` as an `Ident` (identifier)
fn parse_ident<'src>(cst: &CST<'src>) -> Ident<'src> {
    match *cst {
        CST::Ident(ident, ref pos) => Ident::new(ident, pos.clone()),
        _ => cst.pos().error_exit(Invalid("binding")),
    }
}

/// Parse a list of `CST` as the parts of the definition of a static
fn parse_static_def<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> (Ident<'src>, StaticDef<'src>) {
    if let (Some(ident_cst), Some(body_cst)) = (csts.get(0), csts.get(1)) {
        match *ident_cst {
            CST::Ident(name, ref id_pos) => {
                (Ident::new(name, id_pos.clone()),
                 StaticDef { body: parse_expr(&body_cst), pos: pos })
            }
            _ => ident_cst.pos().error_exit(Expected("identifier")),
        }
    } else {
        pos.error_exit(ArityMis(2, csts.len()))
    }
}

/// Parse a first `CST` and some following `CST`s as a procedure and some arguments, i.e. a call
fn parse_sexpr<'src>(func_cst: &CST<'src>,
                     args_csts: &[CST<'src>],
                     pos: SrcPos<'src>)
                     -> Call<'src> {
    let (last, init) =
        args_csts.split_last().map(|(l, i)| (Some(parse_expr(l)), i)).unwrap_or((None, &[]));
    let calls = init.iter().map(parse_expr).fold(parse_expr(func_cst), |func, arg| {
        Expr::Call(Box::new(Call {
            func: func,
            arg: Some(arg),
            typ: Type::Uninferred,
            pos: pos.clone(),
        }))
    });
    Call {
        func: calls,
        arg: last,
        typ: Type::Uninferred,
        pos: pos,
    }
}

/// Parse a list of `CST`s as parts of an `If` conditional
fn parse_if<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> If<'src> {
    if csts.len() != 3 {
        pos.error_exit(ArityMis(3, csts.len()))
    } else {
        If {
            predicate: parse_expr(&csts[0]),
            consequent: parse_expr(&csts[1]),
            alternative: parse_expr(&csts[2]),
            typ: Type::Uninferred,
            pos: pos,
        }
    }
}

fn parse_param<'src>(cst: &CST<'src>) -> Param<'src> {
    Param {
        ident: parse_ident(cst),
        typ: Type::Uninferred,
    }
}

/// Parse a list of `CST`s as the parts of a `Lambda`
fn parse_lambda<'src>(csts: &[CST<'src>], pos: &SrcPos<'src>) -> Lambda<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    match csts[0] {
        CST::SExpr(ref params_csts, _) => {
            Lambda::new_multary(params_csts.iter().map(parse_param).collect(),
                                parse_expr(&csts[1]),
                                pos)
        }
        _ => csts[0].pos().error_exit(Expected("parameter list")),
    }
}

fn collect_pair<T, U, I>(it: I) -> (Vec<T>, Vec<U>)
    where I: Iterator<Item = (T, U)>
{
    let mut v1 = Vec::with_capacity(it.size_hint().0);
    let mut v2 = Vec::with_capacity(it.size_hint().0);
    for (t, u) in it {
        v1.push(t);
        v2.push(u);
    }
    (v1, v2)
}

/// Parse a `let` special form and return as an invocation of a lambda
fn parse_let<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Call<'src> {
    fn parse_binding<'src>(cst: &CST<'src>) -> (Param<'src>, Expr<'src>) {
        match *cst {
            CST::SExpr(ref binding_pair, ref pos) => if binding_pair.len() == 2 {
                (parse_param(&binding_pair[0]), parse_expr(&binding_pair[1]))
            } else {
                pos.error_exit(Expected("pair of variable name and value"))
            },
            ref c => c.pos().error_exit(Expected("variable binding")),
        }
    }

    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }

    let (params, args) = match csts[0] {
        CST::SExpr(ref bindings_csts, _) => collect_pair(bindings_csts.iter().map(parse_binding)),
        ref c => c.pos().error_exit(Expected("list of variable bindings")),
    };

    let l = Lambda::new_multary(params, parse_expr(&csts[1]), &pos);

    Call::new_multary(Expr::Lambda(Box::new(l)), args, pos)
}

/// Parse a list of `CST`s as a `TypeAscript`
fn parse_type_ascript<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> TypeAscript<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    TypeAscript {
        typ: parse_type(&csts[1]),
        expr: parse_expr(&csts[0]),
        pos: pos,
    }
}

/// Parse a list of `CST`s as a `Cons` pair
fn parse_cons<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Cons<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    Cons {
        typ: Type::Uninferred,
        car: parse_expr(&csts[0]),
        cdr: parse_expr(&csts[1]),
        pos: pos,
    }
}

/// Parse a `CST` as an `Expr`
pub fn parse_expr<'src>(cst: &CST<'src>) -> Expr<'src> {
    match *cst {
        CST::SExpr(ref sexpr, ref pos) => {
            if let Some((head, tail)) = sexpr.split_first() {
                match *head {
                    CST::Ident("if", _) => Expr::If(Box::new(parse_if(tail, pos.clone()))),
                    CST::Ident("lambda", _) => {
                        Expr::Lambda(Box::new(parse_lambda(tail, pos)))
                    }
                    CST::Ident("let", _) => {
                        Expr::Call(Box::new(parse_let(tail, pos.clone())))
                    }
                    CST::Ident(":", _) => {
                        Expr::TypeAscript(Box::new(parse_type_ascript(tail, pos.clone())))
                    }
                    CST::Ident("cons", _) => {
                        Expr::Cons(Box::new(parse_cons(tail, pos.clone())))
                    }
                    _ => Expr::Call(Box::new(parse_sexpr(&sexpr[0], tail, pos.clone()))),
                }
            } else {
                Expr::Nil(Nil { pos: pos.clone() })
            }
        }
        CST::Ident("true", ref pos) => {
            Expr::Bool(Bool { val: true, pos: pos.clone() })
        }
        CST::Ident("false", ref pos) => {
            Expr::Bool(Bool { val: false, pos: pos.clone() })
        }
        CST::Ident(ident, ref pos) => {
            Expr::Binding(Binding {
                ident: Ident::new(ident, pos.clone()),
                typ: Type::Uninferred,
            })
        }
        CST::Num(num, ref pos) => {
            Expr::NumLit(NumLit {
                lit: num,
                typ: Type::Uninferred,
                pos: pos.clone(),
            })
        }
        CST::Str(ref s, ref pos) => {
            Expr::StrLit(StrLit {
                lit: s.clone(),
                typ: Type::Uninferred,
                pos: pos.clone(),
            })
        }
    }
}

/// Parse a list of `CST`s as an external procedure declaration
fn parse_extern_proc<'src>(csts: &[CST<'src>],
                           pos: &SrcPos<'src>)
                           -> (Ident<'src>, ExternProcDecl<'src>) {
    if csts.len() != 2 {
        pos.error_exit("Invalid external procedure declaration. Expected identifier and type")
    } else {
        match csts[0] {
            CST::Ident(name, ref id_pos) => {
                let typ = parse_type(&csts[1]);

                if !typ.is_fully_known() {
                    csts[1].pos().error_exit("Type of external static must be fully specified")
                }

                let decl = ExternProcDecl { typ: typ, pos: pos.clone() };

                (Ident::new(name, id_pos.clone()), decl)
            }
            _ => csts[0].pos().error_exit(Expected("identifier")),
        }
    }
}

/// Parse a `CST` as an item. Some items are actually compount items,
/// so a single item tree may expand to multiple items.
fn parse_item<'src>(cst: &CST<'src>) -> Vec<Item<'src>> {
    match *cst {
        CST::SExpr(ref sexpr, ref pos) if !sexpr.is_empty() => {
            match sexpr[0] {
                CST::Ident("define", _) => {
                    let (id, def) = parse_static_def(&sexpr[1..], pos.clone());
                    vec![Item::StaticDef(id, def)]
                }
                CST::Ident("extern-proc", _) => {
                    let (id, decl) = parse_extern_proc(&sexpr[1..], pos);
                    vec![Item::ExternProcDecl(id, decl)]
                }
                _ => vec![Item::Expr(parse_expr(cst))],
            }
        }
        _ => vec![Item::Expr(parse_expr(cst))],
    }
}

/// Parse a list of `CST`s as a list of items
fn parse_items<'src>(csts: &[CST<'src>])
                     -> (HashMap<&'src str, StaticDef<'src>>,
                         HashMap<&'src str, ExternProcDecl<'src>>,
                         Vec<Expr<'src>>) {
    let (mut static_defs, mut extern_funcs) = (HashMap::new(), HashMap::new());
    let mut exprs = Vec::new();

    for item in csts.iter().flat_map(parse_item) {
        match item {
            Item::StaticDef(id, def) => {
                if let Some(def) = static_defs.insert(id.s, def) {
                    def.pos.error_exit(format!("Duplicate static definition `{}`", id.s))
                }
            }
            Item::ExternProcDecl(id, decl) => {
                if let Some(decl) = extern_funcs.insert(id.s, decl) {
                    decl.pos
                        .error_exit(format!("Duplicate external procedure declaration `{}`", id.s))
                }
            }
            Item::Expr(expr) => exprs.push(expr),
        }
    }

    (static_defs, extern_funcs, exprs)
}

/// Parse a list of `CST`s as the items of a `Module`
fn parse_module<'src>(csts: &[CST<'src>]) -> Module<'src> {
    let (static_defs, extern_funcs, exprs) = parse_items(csts);

    for expr in exprs {
        expr.pos().error_exit("Expression at top level");
    }
    Module {
        static_defs: static_defs,
        extern_funcs: extern_funcs,
    }
}


pub fn parse<'src>(csts: &[CST<'src>]) -> Module<'src> {
    parse_module(csts)
}
