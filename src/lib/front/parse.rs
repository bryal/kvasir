// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use self::ParseErr::*;
use super::SrcPos;
use super::ast::*;
use super::lex::CST;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};

/// An item at the top-level. Either a global definition of an external declaration
enum TopLevelItem<'src> {
    GlobDef(Binding<'src>),
    ExternDecl(ExternDecl<'src>),
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

/// Parse a `CST` as a `Type`
pub fn parse_type<'src>(tree: &CST<'src>) -> Type<'src> {
    match *tree {
        // Type application. E.g. `(Vec Int32)`
        CST::SExpr(ref app, ref pos) if !app.is_empty() => {
            match app[0] {
                CST::Ident("->", _) if app.len() < 3 => {
                    pos.error_exit(
                        "Function type constructor requires at least two arguments: \
                         one/multiple input type(s) and an output type",
                    )
                }
                CST::Ident("->", _) if app.len() == 3 => {
                    Type::App("->", vec![parse_type(&app[1]), parse_type(&app[2])])
                }
                CST::Ident("->", _) => {
                    let last_fn = Type::new_func(
                        parse_type(&app[app.len() - 2]),
                        parse_type(&app[app.len() - 1]),
                    );
                    app[1..app.len() - 2].iter().rev().fold(last_fn, |acc, t| {
                        Type::new_func(parse_type(t), acc)
                    })
                }
                _ => app[0].pos().error_exit(Invalid("type constructor")),
            }
        }
        CST::SExpr(_, ref pos) => pos.error_exit("Empty type application"),
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

/// Parse a list of `CST` as the parts of the definition of a global variable
fn parse_global<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Binding<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    } else {
        Binding {
            ident: parse_ident(&csts[0]),
            typ: Type::Uninferred,
            val: parse_expr(&csts[1]),
            pos: pos,
        }
    }
}

/// Parse a first `CST` and some following `CST`s as a procedure and some arguments, i.e. a call
fn parse_sexpr<'src>(
    func_cst: &CST<'src>,
    args_csts: &[CST<'src>],
    pos: SrcPos<'src>,
) -> Call<'src> {
    Call::new_multary(
        parse_expr(func_cst),
        args_csts.iter().map(parse_expr).collect(),
        pos,
    )
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

/// Parse a list of `CST`s as the parts of a `Lambda`
fn parse_lambda<'src>(csts: &[CST<'src>], pos: &SrcPos<'src>) -> Lambda<'src> {
    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }
    match csts[0] {
        CST::SExpr(ref params_csts, ref params_pos) => {
            Lambda::new_multary(
                params_csts
                    .iter()
                    .map(|param_cst| (parse_ident(param_cst), Type::Uninferred))
                    .collect(),
                params_pos,
                parse_expr(&csts[1]),
                pos,
            )
        }
        _ => csts[0].pos().error_exit(Expected("parameter list")),
    }
}

/// Parse a `let` special form and return as an invocation of a lambda
fn parse_let<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Let<'src> {
    fn parse_binding<'src>(cst: &CST<'src>) -> Binding<'src> {
        match *cst {
            CST::SExpr(ref binding_pair, ref pos) => {
                if binding_pair.len() == 2 {
                    Binding {
                        ident: parse_ident(&binding_pair[0]),
                        typ: Type::Uninferred,
                        val: parse_expr(&binding_pair[1]),
                        pos: pos.clone(),
                    }
                } else {
                    pos.error_exit(Expected("pair of variable name and value"))
                }
            }
            ref c => c.pos().error_exit(Expected("variable binding")),
        }
    }

    if csts.len() != 2 {
        pos.error_exit(ArityMis(2, csts.len()))
    }

    let body = parse_expr(&csts[1]);

    match csts[0] {
        CST::SExpr(ref bindings_csts, _) => Let {
            bindings: bindings_csts.iter().map(parse_binding).collect(),
            body: body,
            typ: Type::Uninferred,
            pos: pos.clone(),
        },
        ref c => c.pos().error_exit(Expected("list of variable bindings")),
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
                    CST::Ident("lambda", _) => Expr::Lambda(Box::new(parse_lambda(tail, pos))),
                    CST::Ident("let", _) => Expr::Let(Box::new(parse_let(tail, pos.clone()))),
                    CST::Ident(":", _) => {
                        Expr::TypeAscript(Box::new(parse_type_ascript(tail, pos.clone())))
                    }
                    CST::Ident("cons", _) => Expr::Cons(Box::new(parse_cons(tail, pos.clone()))),
                    _ => Expr::Call(Box::new(parse_sexpr(&sexpr[0], tail, pos.clone()))),
                }
            } else {
                Expr::Nil(Nil { pos: pos.clone() })
            }
        }
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

/// Parse a list of `CST`s as an external variable declaration
fn parse_extern<'src>(csts: &[CST<'src>], pos: &SrcPos<'src>) -> ExternDecl<'src> {
    if csts.len() != 2 {
        pos.error_exit(
            "Invalid external variable declaration. Expected identifier and type",
        )
    } else {
        match csts[0] {
            CST::Ident(name, ref id_pos) => {
                let typ = parse_type(&csts[1]);

                if !typ.is_known_monomorphic() {
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

/// Parse a `CST` as an item
fn parse_top_level_item<'src>(cst: &CST<'src>) -> TopLevelItem<'src> {
    let pos = cst.pos();
    match *cst {
        CST::SExpr(ref sexpr, _) if !sexpr.is_empty() => {
            match sexpr[0] {
                CST::Ident("define", _) => {
                    let binding = parse_global(&sexpr[1..], pos.clone());
                    return TopLevelItem::GlobDef(binding);
                }
                CST::Ident("extern", _) => {
                    let ext = parse_extern(&sexpr[1..], pos);
                    return TopLevelItem::ExternDecl(ext);
                }
                _ => (),
            }
        }
        _ => (),
    }
    pos.error_exit("Unexpected token-tree at top-level")
}

/// Parse a list of `CST`s as the items of a `Module`
fn parse_module<'src>(csts: &[CST<'src>]) -> Module<'src> {
    use self::TopLevelItem::*;
    // Store globals in a Vec as order matters atm, but disallow
    // multiple definitions. Use a set to keep track of defined globals
    let mut defined_globals = HashSet::new();
    let mut globals = Vec::new();
    let mut externs = HashMap::new();
    let mut main = None;

    for item in csts.iter().map(parse_top_level_item) {
        match item {
            GlobDef(binding) => {
                let id = binding.ident.s;
                if id == "main" && main.is_none() {
                    main = Some(binding)
                } else if id != "main" && defined_globals.insert(binding.ident.s) {
                    globals.push(binding)
                } else {
                    binding.pos.error_exit(format!(
                        "Conflicting definition of variable `{}`",
                        binding.ident.s
                    ))
                }
            }
            ExternDecl(ext) => {
                if let Some(ext) = externs.insert(ext.ident.s, ext) {
                    ext.pos.error_exit(format!(
                        "Duplicate declaration of external variable `{}`",
                        ext.ident.s
                    ))
                }
            }
        }
    }
    Module {
        globals,
        externs,
        main,
    }
}


pub fn parse<'src>(csts: &[CST<'src>]) -> Module<'src> {
    parse_module(csts)
}
