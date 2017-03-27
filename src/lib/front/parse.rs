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
                    Type::Construct(constructor, construct[1..].iter().map(parse_type).collect())
                }
                _ => construct[0].pos().error_exit(Invalid("type constructor")),
            }
        }
        CST::SExpr(_, ref pos) => pos.error_exit("Empty type construction"),
        CST::Ident("_", _) => Type::Unknown,
        CST::Ident("Nil", _) => TYPE_NIL.clone(),
        CST::Ident(basic, _) => Type::Basic(basic),
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
fn parse_sexpr<'src>(proc_cst: &CST<'src>,
                     args_csts: &[CST<'src>],
                     pos: SrcPos<'src>)
                     -> Call<'src> {
    Call {
        proced: parse_expr(proc_cst),
        args: args_csts.iter().map(parse_expr).collect(),
        pos: pos,
    }
}

/// Parse a list of `CST`s as a `Block`.
/// Returns `None` if there are no expressions in the block.
fn parse_block<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Option<Block<'src>> {
    let (static_defs, extern_funcs, exprs) = parse_items(csts);

    if exprs.is_empty() {
        None
    } else {
        Some(Block {
            static_defs: static_defs,
            extern_funcs: extern_funcs,
            exprs: exprs,
            pos: pos,
        })
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
            pos: pos,
        }
    }
}

/// Parse a list of `CST`s as the parts of a `Lambda`
fn parse_lambda<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Lambda<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    match csts[0] {
        CST::SExpr(ref params_csts, _) => {
            Lambda {
                params: params_csts.iter()
                                   .map(|param_cst| {
                                       Param::new(parse_ident(param_cst), Type::Unknown)
                                   })
                                   .collect(),
                body: parse_expr(&csts[1]),
                pos: pos,
            }
        }
        _ => csts[0].pos().error_exit(Expected("parameter list")),
    }
}

/// Parse a list of `CST`s as the parts of a `VarDef`
fn parse_var_def<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> VarDef<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    match csts[0] {
        CST::Ident(binding, ref binding_pos) => {
            VarDef {
                binding: Ident::new(binding, binding_pos.clone()),
                body: parse_expr(&csts[1]),
                typ: Type::Unknown,
                pos: pos,
            }
        }
        _ => csts[0].pos().error_exit(Expected("identifier")),
    }
}

/// Parse a list of `CST`s as the parts of an `Assign`
fn parse_assign<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Assign<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    Assign {
        lhs: parse_expr(&csts[0]),
        rhs: parse_expr(&csts[1]),
        typ: Type::Unknown,
        pos: pos,
    }
}

/// Parse a `CST` as an expression to `Transmute`
fn parse_transmute<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Transmute<'src> {
    if csts.len() != 1 {
        pos.error_exit(ArityMis(1, csts.len()))
    }
    Transmute {
        arg: parse_expr(&csts[0]),
        typ: Type::Unknown,
        pos: pos,
    }
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

/// Parse a `CST` as an `Expr`
pub fn parse_expr<'src>(cst: &CST<'src>) -> Expr<'src> {
    match *cst {
        CST::SExpr(ref sexpr, ref pos) => {
            if let Some((head, tail)) = sexpr.split_first() {
                match *head {
                    CST::Ident("if", _) => Expr::If(Box::new(parse_if(tail, pos.clone()))),
                    CST::Ident("lambda", _) => {
                        Expr::Lambda(Box::new(parse_lambda(tail, pos.clone())))
                    }
                    CST::Ident("begin", _) => {
                        parse_block(tail, pos.clone())
                            .map(|block| Expr::Block(Box::new(block)))
                            .unwrap_or(Expr::Nil(Nil { typ: Type::Unknown, pos: pos.clone() }))
                    }
                    CST::Ident("def-var", _) => {
                        Expr::VarDef(Box::new(parse_var_def(tail, pos.clone())))
                    }
                    CST::Ident("set", _) => Expr::Assign(Box::new(parse_assign(tail, pos.clone()))),
                    CST::Ident("transmute", _) => {
                        Expr::Transmute(Box::new(parse_transmute(tail, pos.clone())))
                    }
                    CST::Ident(":", _) => {
                        Expr::TypeAscript(Box::new(parse_type_ascript(tail, pos.clone())))
                    }
                    _ => Expr::Call(Box::new(parse_sexpr(&sexpr[0], tail, pos.clone()))),
                }
            } else {
                Expr::Nil(Nil { typ: Type::Unknown, pos: pos.clone() })
            }
        }
        CST::Ident("true", ref pos) => {
            Expr::Bool(Bool {
                val: true,
                typ: Type::Unknown,
                pos: pos.clone(),
            })
        }
        CST::Ident("false", ref pos) => {
            Expr::Bool(Bool {
                val: false,
                typ: Type::Unknown,
                pos: pos.clone(),
            })
        }
        CST::Ident(ident, ref pos) => {
            Expr::Binding(Binding {
                ident: Ident::new(ident, pos.clone()),
                typ: Type::Unknown,
            })
        }
        CST::Num(num, ref pos) => {
            Expr::NumLit(NumLit {
                lit: num,
                typ: Type::Unknown,
                pos: pos.clone(),
            })
        }
        CST::Str(ref s, ref pos) => {
            Expr::StrLit(StrLit {
                lit: s.clone(),
                typ: Type::Unknown,
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
                CST::Ident("def-static", _) => {
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
