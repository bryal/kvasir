// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use std::collections::HashMap;
use std::fmt::{self, Display};
use super::SrcPos;
use super::lex::CST;
use super::ast::*;
use self::ParseErr::*;

enum ParseErr {
    Invalid(&'static str),
    Mismatch(&'static str, &'static str),
    ArityMis(usize, usize),
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

/// An object that parses `CST`s as different kinds of `Module` items
struct Parser;

impl<'src> Parser {
    /// Parse a `CST` as a `Type`
    pub fn parse_type(tree: &CST<'src>) -> Type<'src> {
        match *tree {
            // Type construction. E.g. `(Vec Int32)`
            CST::SExpr(ref construct, _) if !construct.is_empty() => {
                match construct[0] {
                    CST::Ident(constructor, _) => {
                        Type::Construct(constructor,
                                        construct[1..].iter().map(Self::parse_type).collect())
                    }
                    _ => construct[0].pos().error(Invalid("type constructor")),
                }
            }
            CST::SExpr(_, ref pos) => pos.error("Empty type construction"),
            CST::List(_, ref pos) => pos.error("Expected type, found syntax list (`[...]`)"),
            CST::Ident("_", _) => Type::Unknown,
            CST::Ident("Nil", _) => TYPE_NIL.clone(),
            CST::Ident(basic, _) => Type::Basic(basic),
            CST::Num(_, ref pos) => pos.error(Mismatch("type", "numeric literal")),
            CST::Str(_, ref pos) => pos.error(Mismatch("type", "string literal")),
        }
    }

    /// Parse a `CST` as an `Ident` (identifier)
    fn parse_ident(cst: &CST<'src>) -> Ident<'src> {
        match *cst {
            CST::Ident(ident, ref pos) => Ident::new(ident, pos.clone()),
            _ => cst.pos().error(Invalid("binding")),
        }
    }

    /// Parse a `CST` as a `Path`
    fn parse_path(cst: &CST<'src>) -> Path<'src> {
        match *cst {
            CST::Ident(s, ref pos) => Path::from_str(s, pos.clone()),
            _ => cst.pos().error(Expected("path")),
        }
    }

    /// Parse a `CST` as a tree of `Path`s, returning a vec of the canonicalized form
    /// of the path in each leaf.
    /// E.g. `(a\b (c w x) y z)` corresponds to the canonicalized paths
    /// `a\b\c\w`, `a\b\c\x`, `a\b\y`, `a\b\z`
    fn parse_paths_tree(cst: &CST<'src>) -> Vec<Path<'src>> {
        match *cst {
            CST::SExpr(ref compound, ref pos) => {
                if let Some((chead, tail)) = compound.split_first() {
                    let path_head = Self::parse_path(chead);
                    tail.iter()
                        .map(Self::parse_paths_tree)
                        .flat_map(|v| v)
                        .map(|sub| {
                            path_head.clone()
                                     .concat(&sub)
                                     .unwrap_or_else(|_| sub.pos.error("Sub-path is absolute"))
                        })
                        .collect()
                } else {
                    pos.error("Empty path compound")
                }
            }
            CST::Ident(ident, ref pos) => vec![Path::from_str(ident, pos.clone())],
            CST::Num(_, ref pos) => pos.error("Expected path, found numeric literal"),
            CST::Str(_, ref pos) => pos.error("Expected path, found string literal"),
            CST::List(_, ref pos) => pos.error("Expected path, found syntax list"),
        }
    }

    /// Parse a list of `CST`s as a list of trees of paths to `Use`
    fn parse_use(csts: &[CST<'src>], pos: &SrcPos<'src>) -> Vec<Use<'src>> {
        csts.iter()
            .map(Self::parse_paths_tree)
            .flat_map(|paths| paths)
            .map(|path| {
                Use {
                    path: path,
                    pos: pos.clone(),
                }
            })
            .collect()
    }

    /// Parse a list of `CST` as the parts of a constant definition
    fn parse_const_def(csts: &[CST<'src>], pos: SrcPos<'src>) -> (Ident<'src>, ConstDef<'src>) {
        if let (Some(ident_cst), Some(body_cst)) = (csts.get(0), csts.get(1)) {
            match *ident_cst {
                CST::Ident(name, ref id_pos) => {
                    (Ident::new(name, id_pos.clone()),
                     ConstDef {
                        body: Self::parse_expr(&body_cst),
                        pos: pos,
                    })
                }
                _ => ident_cst.pos().error(Expected("identifier")),
            }
        } else {
            pos.error(ArityMis(2, csts.len()))
        }
    }

    /// Parse a first `CST` and some following `CST`s as a procedure and some arguments, i.e. a call
    fn parse_sexpr(proc_cst: &CST<'src>, args_csts: &[CST<'src>], pos: SrcPos<'src>) -> Call<'src> {
        Call {
            proced: Self::parse_expr(proc_cst),
            args: args_csts.iter().map(Self::parse_expr).collect(),
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as a `Block`.
    /// Returns `None` if there are no expressions in the block.
    fn parse_block(csts: &[CST<'src>], pos: SrcPos<'src>) -> Option<Block<'src>> {
        let (uses, const_defs, extern_funcs, exprs) = Parser::parse_items(csts);

        if exprs.is_empty() {
            None
        } else {
            Some(Block {
                uses: uses,
                const_defs: const_defs,
                extern_funcs: extern_funcs,
                exprs: exprs,
                pos: pos,
            })
        }
    }

    /// Parse a list of `CST`s as parts of an `If` conditional
    fn parse_if(csts: &[CST<'src>], pos: SrcPos<'src>) -> If<'src> {
        if csts.len() != 3 {
            pos.error(ArityMis(3, csts.len()))
        } else {
            If {
                predicate: Self::parse_expr(&csts[0]),
                consequent: Self::parse_expr(&csts[1]),
                alternative: Self::parse_expr(&csts[2]),
                pos: pos,
            }
        }
    }

    /// Parse a list of `CST`s as the parts of a `Lambda`
    fn parse_lambda(csts: &[CST<'src>], pos: SrcPos<'src>) -> Lambda<'src> {
        if csts.len() != 2 {
            pos.error(ArityMis(2, csts.len()))
        }
        match csts[0] {
            CST::List(ref params_csts, _) => {
                Lambda {
                    params: params_csts.iter()
                                       .map(|param_cst| {
                                           Param::new(Self::parse_ident(param_cst), Type::Unknown)
                                       })
                                       .collect(),
                    body: Self::parse_expr(&csts[1]),
                    pos: pos,
                }
            }
            _ => csts[0].pos().error(Expected("list")),
        }
    }

    /// Parse a list of `CST`s as the parts of a `VarDef`
    fn parse_var_def(csts: &[CST<'src>], pos: SrcPos<'src>) -> VarDef<'src> {
        if csts.len() != 2 {
            pos.error(ArityMis(2, csts.len()))
        }
        match csts[0] {
            CST::Ident(binding, ref binding_pos) => {
                VarDef {
                    binding: Ident::new(binding, binding_pos.clone()),
                    mutable: false,
                    body: Self::parse_expr(&csts[1]),
                    typ: Type::Unknown,
                    pos: pos,
                }
            }
            _ => csts[0].pos().error(Expected("list")),
        }
    }

    /// Parse a list of `CST`s as the parts of an `Assign`
    fn parse_assign(csts: &[CST<'src>], pos: SrcPos<'src>) -> Assign<'src> {
        if csts.len() != 2 {
            pos.error(ArityMis(2, csts.len()))
        }
        Assign {
            lhs: Self::parse_expr(&csts[0]),
            rhs: Self::parse_expr(&csts[1]),
            typ: Type::Unknown,
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as the parts of a `Deref`
    fn parse_deref(csts: &[CST<'src>], pos: SrcPos<'src>) -> Deref<'src> {
        if csts.len() != 1 {
            pos.error(ArityMis(1, csts.len()))
        }
        Deref {
            r: Self::parse_expr(&csts[0]),
            pos: pos,
        }
    }

    /// Parse a `CST` as an expression to `Transmute`
    fn parse_transmute(csts: &[CST<'src>], pos: SrcPos<'src>) -> Transmute<'src> {
        if csts.len() != 1 {
            pos.error(ArityMis(1, csts.len()))
        }
        Transmute {
            arg: Self::parse_expr(&csts[0]),
            typ: Type::Unknown,
            pos: pos,
        }
    }

    /// Parse a list of `CST`s as a `TypeAscript`
    fn parse_type_ascript(csts: &[CST<'src>], pos: SrcPos<'src>) -> TypeAscript<'src> {
        if csts.len() != 2 {
            pos.error(ArityMis(2, csts.len()))
        }
        TypeAscript {
            typ: Self::parse_type(&csts[1]),
            expr: Self::parse_expr(&csts[0]),
            pos: pos,
        }
    }

    /// Parse a `CST` as an `Expr`
    fn parse_quoted_expr(cst: &CST<'src>) -> Expr<'src> {
        match *cst {
            CST::SExpr(ref list, ref pos) => {
                Expr::Call(Box::new(Call {
                    proced: Expr::Binding(Binding {
                        path: Path::from_str("list", pos.clone()),
                        typ: Type::Unknown,
                    }),
                    args: list.iter()
                              .map(|li| Self::parse_quoted_expr(li))
                              .collect(),
                    pos: pos.clone(),
                }))
            }
            CST::List(_, ref pos) => pos.error("Expected expression, found syntax list"),
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
    pub fn parse_expr(cst: &CST<'src>) -> Expr<'src> {
        match *cst {
            CST::SExpr(ref sexpr, ref pos) => {
                if let Some((head, tail)) = sexpr.split_first() {
                    match *head {
                        CST::Ident("quote", _) => {
                            if let Some(to_quote) = tail.first() {
                                Self::parse_quoted_expr(to_quote)
                            } else {
                                pos.error(ArityMis(1, sexpr.len()))
                            }
                        }
                        CST::Ident("if", _) => {
                            Expr::If(Box::new(Self::parse_if(tail, pos.clone())))
                        }
                        CST::Ident("lambda", _) => {
                            Expr::Lambda(Box::new(Self::parse_lambda(tail, pos.clone())))
                        }
                        CST::Ident("block", _) => {
                            Self::parse_block(tail, pos.clone())
                                .map(|block| Expr::Block(Box::new(block)))
                                .unwrap_or(Expr::Nil(Nil {
                                    typ: Type::Unknown,
                                    pos: pos.clone(),
                                }))
                        }
                        CST::Ident("def-var", _) => {
                            Expr::VarDef(Box::new(Self::parse_var_def(tail, pos.clone())))
                        }
                        CST::Ident("def-var-mut", _) => {
                            Expr::VarDef(Box::new(VarDef {
                                mutable: true,
                                ..Self::parse_var_def(tail, pos.clone())
                            }))
                        }
                        CST::Ident("set", _) => {
                            Expr::Assign(Box::new(Self::parse_assign(tail, pos.clone())))
                        }
                        CST::Ident("deref", _) => {
                            Expr::Deref(Box::new(Self::parse_deref(tail, pos.clone())))
                        }
                        CST::Ident("transmute", _) => {
                            Expr::Transmute(Box::new(Self::parse_transmute(tail, pos.clone())))
                        }
                        CST::Ident(":", _) => {
                            Expr::TypeAscript(Box::new(Self::parse_type_ascript(tail, pos.clone())))
                        }
                        _ => Expr::Call(Box::new(Self::parse_sexpr(&sexpr[0], tail, pos.clone()))),
                    }
                } else {
                    Expr::Nil(Nil {
                        typ: Type::Unknown,
                        pos: pos.clone(),
                    })
                }
            }
            CST::List(_, ref pos) => pos.error("Expected expression, found syntax list"),
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

    /// Parse a list of `CST`s as an external constant declaration
    fn parse_extern_const(csts: &[CST<'src>], pos: &SrcPos<'src>) -> (Ident<'src>, Type<'src>) {
        if csts.len() != 2 {
            pos.error("Invalid external constant declaration. Expected identifier and type")
        } else {
            match csts[0] {
                CST::Ident(name, ref id_pos) => {
                    let typ = Self::parse_type(&csts[1]);

                    if !typ.is_fully_known() {
                        csts[1].pos().error("Type of external constant must be fully specified")
                    }
                    (Ident::new(name, id_pos.clone()), typ)
                }
                _ => csts[0].pos().error(Expected("identifier")),
            }
        }
    }

    /// Parse a list of `CST`s as a list of items
    fn parse_items(csts: &[CST<'src>])
                   -> (Vec<Use<'src>>,
                       HashMap<Ident<'src>, ConstDef<'src>>,
                       HashMap<Ident<'src>, Type<'src>>,
                       Vec<Expr<'src>>) {
        let mut uses = Vec::new();
        let (mut const_defs, mut extern_funcs) = (HashMap::new(), HashMap::new());
        let mut exprs = Vec::new();

        for cst in csts {
            match *cst {
                CST::SExpr(ref sexpr, ref pos) if !sexpr.is_empty() => {
                    match sexpr[0] {
                        CST::Ident("use", _) => uses.extend(Self::parse_use(&sexpr[1..], pos)),
                        CST::Ident("def-const", _) => {
                            let (id, def) = Self::parse_const_def(&sexpr[1..], pos.clone());
                            let id_s = id.s;

                            if const_defs.insert(id, def).is_some() {
                                pos.error(format!("Duplicate constant definition `{}`", id_s))
                            }
                        }
                        CST::Ident("extern-proc", _) => {
                            let (id, typ) = Self::parse_extern_const(&sexpr[1..], pos);
                            let id_s = id.s;

                            if extern_funcs.insert(id, typ).is_some() {
                                pos.error(format!("Duplicate external constant declaration `{}`",
                                                  id_s))
                            }
                        }
                        _ => exprs.push(Self::parse_expr(cst)),
                    }
                }
                _ => exprs.push(Self::parse_expr(cst)),
            }
        }

        (uses, const_defs, extern_funcs, exprs)
    }

    /// Parse a list of `CST`s as the items of a `Module`
    fn parse_ast(csts: &[CST<'src>]) -> Module<'src> {
        let (uses, const_defs, extern_funcs, exprs) = Self::parse_items(csts);

        for expr in exprs {
            expr.pos().error("Expression at top level");
        }
        Module {
            uses: uses,
            const_defs: const_defs,
            extern_funcs: extern_funcs,
        }
    }
}

pub fn parse<'src>(csts: &[CST<'src>]) -> Module<'src> {
    Parser::parse_ast(csts)
}
