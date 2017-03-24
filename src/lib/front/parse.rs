// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use std::collections::HashMap;
use std::fmt::{self, Display};
use super::SrcPos;
use super::lex::CST;
use super::ast::*;
use self::ParseErr::*;

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
        CST::List(_, ref pos) => pos.error_exit("Expected type, found syntax list (`[...]`)"),
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

/// Parse a `CST` as a `Path`
fn parse_path<'src>(cst: &CST<'src>) -> Path<'src> {
    match *cst {
        CST::Ident(s, ref pos) => Path::from_str(s, pos.clone()),
        _ => cst.pos().error_exit(Expected("path")),
    }
}

/// Parse a `CST` as a tree of `Path`s, returning a vec of the canonicalized form
/// of the path in each leaf.
/// E.g. `(a\b (c w x) y z)` corresponds to the canonicalized paths
/// `a\b\c\w`, `a\b\c\x`, `a\b\y`, `a\b\z`
fn parse_paths_tree<'src>(cst: &CST<'src>) -> Vec<Path<'src>> {
    match *cst {
        CST::SExpr(ref compound, ref pos) => {
            if let Some((chead, tail)) = compound.split_first() {
                let path_head = parse_path(chead);
                tail.iter()
                    .map(parse_paths_tree)
                    .flat_map(|v| v)
                    .map(|sub| {
                        path_head.clone()
                                 .concat(&sub)
                                 .unwrap_or_else(|_| sub.pos.error_exit("Sub-path is absolute"))
                    })
                    .collect()
            } else {
                pos.error_exit("Empty path compound")
            }
        }
        CST::Ident(ident, ref pos) => vec![Path::from_str(ident, pos.clone())],
        CST::Num(_, ref pos) => pos.error_exit("Expected path, found numeric literal"),
        CST::Str(_, ref pos) => pos.error_exit("Expected path, found string literal"),
        CST::List(_, ref pos) => pos.error_exit("Expected path, found syntax list"),
    }
}

/// Parse a list of `CST`s as a list of trees of paths to `Use`
fn parse_use<'src>(csts: &[CST<'src>], pos: &SrcPos<'src>) -> Vec<Use<'src>> {
    csts.iter()
        .map(parse_paths_tree)
        .flat_map(|paths| paths)
        .map(|path| {
            Use {
                path: path,
                pos: pos.clone(),
            }
        })
        .collect()
}

/// Parse a list of `CST` as the parts of the definition of a static
fn parse_static_def<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> (Ident<'src>, StaticDef<'src>) {
    if let (Some(ident_cst), Some(body_cst)) = (csts.get(0), csts.get(1)) {
        match *ident_cst {
            CST::Ident(name, ref id_pos) => {
                (Ident::new(name, id_pos.clone()),
                 StaticDef {
                    body: parse_expr(&body_cst),
                    pos: pos,
                })
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
    let (uses, static_defs, extern_funcs, exprs) = parse_items(csts);

    if exprs.is_empty() {
        None
    } else {
        Some(Block {
            uses: uses,
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
        CST::List(ref params_csts, _) => {
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
        _ => csts[0].pos().error_exit(Expected("list")),
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
                mutable: false,
                body: parse_expr(&csts[1]),
                typ: Type::Unknown,
                pos: pos,
            }
        }
        _ => csts[0].pos().error_exit(Expected("list")),
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

/// Parse a list of `CST`s as the parts of a `Deref`
fn parse_deref<'src>(csts: &[CST<'src>], pos: SrcPos<'src>) -> Deref<'src> {
    if csts.len() != 1 {
        pos.error_exit(ArityMis(1, csts.len()))
    }
    Deref {
        r: parse_expr(&csts[0]),
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
fn parse_quoted_expr<'src>(cst: &CST<'src>) -> Expr<'src> {
    match *cst {
        CST::SExpr(ref list, ref pos) => {
            Expr::Call(Box::new(Call {
                proced: Expr::Binding(Binding {
                    path: Path::from_str("list", pos.clone()),
                    typ: Type::Unknown,
                }),
                args: list.iter()
                          .map(|li| parse_quoted_expr(li))
                          .collect(),
                pos: pos.clone(),
            }))
        }
        CST::List(_, ref pos) => pos.error_exit("Expected expression, found syntax list"),
        CST::Ident(ident, ref pos) => {
            Expr::Symbol(Symbol {
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

/// Parse a `CST` as an `Expr`
pub fn parse_expr<'src>(cst: &CST<'src>) -> Expr<'src> {
    match *cst {
        CST::SExpr(ref sexpr, ref pos) => {
            if let Some((head, tail)) = sexpr.split_first() {
                match *head {
                    CST::Ident("quote", _) => {
                        if let Some(to_quote) = tail.first() {
                            parse_quoted_expr(to_quote)
                        } else {
                            pos.error_exit(ArityMis(1, sexpr.len()))
                        }
                    }
                    CST::Ident("if", _) => Expr::If(Box::new(parse_if(tail, pos.clone()))),
                    CST::Ident("lambda", _) => {
                        Expr::Lambda(Box::new(parse_lambda(tail, pos.clone())))
                    }
                    CST::Ident("block", _) => {
                        parse_block(tail, pos.clone())
                            .map(|block| Expr::Block(Box::new(block)))
                            .unwrap_or(Expr::Nil(Nil {
                                typ: Type::Unknown,
                                pos: pos.clone(),
                            }))
                    }
                    CST::Ident("def-var", _) => {
                        Expr::VarDef(Box::new(parse_var_def(tail, pos.clone())))
                    }
                    CST::Ident("def-var-mut", _) => {
                        Expr::VarDef(Box::new(VarDef {
                            mutable: true,
                            ..parse_var_def(tail, pos.clone())
                        }))
                    }
                    CST::Ident("set", _) => Expr::Assign(Box::new(parse_assign(tail, pos.clone()))),
                    CST::Ident("deref", _) => Expr::Deref(Box::new(parse_deref(tail, pos.clone()))),
                    CST::Ident("transmute", _) => {
                        Expr::Transmute(Box::new(parse_transmute(tail, pos.clone())))
                    }
                    CST::Ident(":", _) => {
                        Expr::TypeAscript(Box::new(parse_type_ascript(tail, pos.clone())))
                    }
                    _ => Expr::Call(Box::new(parse_sexpr(&sexpr[0], tail, pos.clone()))),
                }
            } else {
                Expr::Nil(Nil {
                    typ: Type::Unknown,
                    pos: pos.clone(),
                })
            }
        }
        CST::List(_, ref pos) => pos.error_exit("Expected expression, found syntax list"),
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
                path: Path::from_str(ident, pos.clone()),
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

                let decl = ExternProcDecl {
                    typ: typ,
                    pos: pos.clone(),
                };

                (Ident::new(name, id_pos.clone()), decl)
            }
            _ => csts[0].pos().error_exit(Expected("identifier")),
        }
    }
}

macro_rules! attribute_struct_parser {
    ($attr_name: expr;
     $fn_name: ident -> $ret_ty: ty;
     $struct_init: expr;
     [$( ($field: ident, $field_str: expr) ),*]) => {
        fn $fn_name<'src>(csts: &[CST<'src>]) -> $ret_ty {
            $( let mut $field = None; )*

            for cst in csts {
                match *cst {
                    CST::List(ref list, ref list_pos) if list.len() == 2 => {
                        match list[0] {
                            $(
                            CST::Ident($field_str, _) => {
                                if let CST::Str(ref s, _) = list[1] {
                                    $field = Some(s.clone());
                                } else {
                                    list[1].pos().error_exit(format!(
                                        "Invalid value for field `{}`. Expected string",
                                        $field_str))
                                }
                            }
                            )*
                            CST::Ident(n, ref field_pos) => {
                                field_pos.error_exit("Attribute `{}` has no field named `{}`", $attr_name, n)
                            }
                            _ => list_pos.error_exit("Expected field name (ident)"),
                        }
                    }
                    _ => cst.pos().error_exit("Expected `[FIELD VALUE]` pair"),
                }
            }

            let mut s = $struct_init;
            $( s.$field = $field; )*
            s
        }
    }
}

/// Parse a `CST` as an item. Some items are actually compount items,
/// so a single item tree may expand to multiple items.
fn parse_item<'src>(cst: &CST<'src>) -> Vec<Item<'src>> {
    match *cst {
        CST::SExpr(ref sexpr, ref pos) if !sexpr.is_empty() => {
            match sexpr[0] {
                CST::Ident("use", _) => {
                    parse_use(&sexpr[1..], pos).into_iter().map(Item::Use).collect()
                }
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
                     -> (Vec<Use<'src>>,
                         HashMap<Ident<'src>, StaticDef<'src>>,
                         HashMap<Ident<'src>, ExternProcDecl<'src>>,
                         Vec<Expr<'src>>) {
        let mut uses = Vec::new();
        let (mut static_defs, mut extern_funcs) = (HashMap::new(), HashMap::new());
        let mut exprs = Vec::new();

        for item in csts.iter().flat_map(parse_item) {
            match item {
                Item::Use(u) => uses.push(u),
                Item::StaticDef(id, def) => {
                    let id_s = id.s;
                    if let Some(def) = static_defs.insert(id, def) {
                        def.pos.error_exit(format!("Duplicate static definition `{}`", id_s))
                    }
                }
                Item::ExternProcDecl(id, decl) => {
                    let id_s = id.s;
                    if let Some(decl) = extern_funcs.insert(id, decl) {
                        decl.pos
                            .error_exit(format!("Duplicate external procedure declaration `{}`", id_s))
                    }
                }
                Item::Expr(expr) => exprs.push(expr),
            }
        }

        (uses, static_defs, extern_funcs, exprs)
}

/// Parse a list of `CST`s as the items of a `Module`
fn parse_module<'src>(csts: &[CST<'src>]) -> Module<'src> {
    let (uses, static_defs, extern_funcs, exprs) = parse_items(csts);

    for expr in exprs {
        expr.pos().error_exit("Expression at top level");
    }
    Module {
        uses: uses,
        static_defs: static_defs,
        extern_funcs: extern_funcs,
    }
}


pub fn parse<'src>(csts: &[CST<'src>]) -> Module<'src> {
    parse_module(csts)
}
