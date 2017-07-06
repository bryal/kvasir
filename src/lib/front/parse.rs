// FIXME: ArityMiss is not very descriptive. Customize message for each error case

use self::ParseErr::*;
use super::*;
use super::ast::*;
use super::lex::CST;
use std::collections::HashMap;
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

struct Parser<'tvg> {
    /// Counter for generation of unique type variable ids
    type_var_gen: &'tvg mut TypeVarGen,
}

impl<'tvg> Parser<'tvg> {
    fn new(type_var_gen: &'tvg mut TypeVarGen) -> Self {
        Parser { type_var_gen }
    }

    fn gen_type_var<'src>(&mut self) -> Type<'src> {
        Type::Var(self.type_var_gen.gen())
    }

    /// Parse a `CST` as a `Type`
    fn parse_type<'src>(&mut self, tree: &CST<'src>) -> Type<'src> {
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
                        Type::new_func(self.parse_type(&app[1]), self.parse_type(&app[2]))
                    }
                    CST::Ident("->", _) => {
                        let last_fn = Type::new_func(
                            self.parse_type(&app[app.len() - 2]),
                            self.parse_type(&app[app.len() - 1]),
                        );
                        app[1..app.len() - 2].iter().rev().fold(last_fn, |acc, t| {
                            Type::new_func(self.parse_type(t), acc)
                        })
                    }
                    CST::Ident("Cons", _) if app.len() == 3 => {
                        Type::new_cons(self.parse_type(&app[1]), self.parse_type(&app[2]))
                    }
                    CST::Ident("Cons", _) => pos.error_exit(ArityMis(2, app.len() - 1)),
                    CST::Ident(c, ref c_pos) => {
                        c_pos.error_exit(format!("Undefined type constructor `{}`", c))
                    }
                    _ => app[0].pos().error_exit(Invalid("type constructor")),
                }
            }
            CST::SExpr(_, ref pos) => pos.error_exit("Empty type application"),
            CST::Ident("_", _) => self.gen_type_var(),
            CST::Ident("Nil", _) => TYPE_NIL.clone(),
            CST::Ident(basic, _) => Type::Const(basic),
            CST::Num(_, ref pos) => pos.error_exit(Mismatch("type", "numeric literal")),
            CST::Str(_, ref pos) => pos.error_exit(Mismatch("type", "string literal")),
        }
    }

    /// Parse a `CST` as an `Ident` (identifier)
    fn parse_ident<'src>(&mut self, cst: &CST<'src>) -> Ident<'src> {
        match *cst {
            CST::Ident(ident, ref pos) => Ident::new(ident, pos.clone()),
            _ => cst.pos().error_exit(Invalid("binding")),
        }
    }

    /// Parse a list of `CST` as the parts of the definition of a global variable
    fn parse_global<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Binding<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        } else {
            Binding {
                ident: self.parse_ident(&csts[0]),
                typ: self.gen_type_var(),
                val: self.parse_expr(&csts[1]),
                mono_insts: HashMap::new(),
                pos: pos,
            }
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

    fn parse_binding<'src>(&mut self, cst: &CST<'src>) -> Binding<'src> {
        match *cst {
            CST::SExpr(ref binding_pair, ref pos) => {
                if binding_pair.len() == 2 {
                    Binding {
                        ident: self.parse_ident(&binding_pair[0]),
                        typ: self.gen_type_var(),
                        val: self.parse_expr(&binding_pair[1]),
                        mono_insts: HashMap::new(),
                        pos: pos.clone(),
                    }
                } else {
                    pos.error_exit(Expected("pair of variable name and value"))
                }
            }
            ref c => c.pos().error_exit(Expected("variable binding")),
        }
    }

    /// Parse a `let` special form and return as an invocation of a lambda
    fn parse_let<'src>(&mut self, csts: &[CST<'src>], pos: SrcPos<'src>) -> Let<'src> {
        if csts.len() != 2 {
            pos.error_exit(ArityMis(2, csts.len()))
        }

        let body = self.parse_expr(&csts[1]);

        match csts[0] {
            CST::SExpr(ref bindings_csts, _) => Let {
                bindings: bindings_csts
                    .iter()
                    .map(|c| {
                        let b = self.parse_binding(c);
                        (b.ident.s, b)
                    })
                    .collect(),
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
                        _ => Expr::App(Box::new(self.parse_app(&sexpr[0], tail, pos.clone()))),
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

    /// Parse a list of `CST`s as an external variable declaration
    fn parse_extern<'src>(&mut self, csts: &[CST<'src>], pos: &SrcPos<'src>) -> ExternDecl<'src> {
        if csts.len() != 2 {
            pos.error_exit(
                "Invalid external variable declaration. Expected identifier and type",
            )
        } else {
            match csts[0] {
                CST::Ident(name, ref id_pos) => {
                    let typ = self.parse_type(&csts[1]);

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

    /// Parse a `CST` as an item
    fn parse_top_level_item<'src>(&mut self, cst: &CST<'src>) -> TopLevelItem<'src> {
        let pos = cst.pos();
        match *cst {
            CST::SExpr(ref sexpr, _) if !sexpr.is_empty() => {
                match sexpr[0] {
                    CST::Ident("define", _) => {
                        let binding = self.parse_global(&sexpr[1..], pos.clone());
                        return TopLevelItem::GlobDef(binding);
                    }
                    CST::Ident("extern", _) => {
                        let ext = self.parse_extern(&sexpr[1..], pos);
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
    fn parse_module<'src>(&mut self, csts: &[CST<'src>]) -> Module<'src> {
        use self::TopLevelItem::*;
        // Store globals in a Vec as order matters atm, but disallow
        // multiple definitions. Use a set to keep track of defined globals
        let mut globals = HashMap::new();
        let mut externs = HashMap::new();

        for item in csts.iter().map(|c| self.parse_top_level_item(c)) {
            match item {
                GlobDef(binding) => {
                    let (new_id, new_pos) = (binding.ident.s, binding.pos.clone());
                    if let Some(prev_binding) = globals.insert(new_id, binding) {
                        new_pos.error_exit(format!(
                            "Conflicting definition of variable `{}`\n\
                             Previous definition here `{:?}`",
                            new_id,
                            prev_binding.pos
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
        Module { globals, externs }
    }
}

pub fn parse<'src>(csts: &[CST<'src>], type_var_generator: &mut TypeVarGen) -> Module<'src> {
    let mut parser = Parser::new(type_var_generator);
    parser.parse_module(csts)
}
