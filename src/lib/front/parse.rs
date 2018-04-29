use self::PErr::*;
use super::*;
use super::ast::*;
use super::cst::Cst;
use super::dependency_graph::*;
use lib::CanonPathBuf;
use lib::collections::AddMap;
use lib::front::lex::lex_file;
use std::collections::BTreeMap;
use std::mem;

/// Constructors for common parse errors to prevent repetition and spelling mistakes
#[derive(PartialEq, Eq)]
enum PErr<'s> {
    /// Mismatch in the amount of parameters given. Some amount was expected, another was given
    ArityMis(SrcPos<'s>, usize, usize),
    /// Mismatch in the amount of parameters given. At least some amount was expected, another was given
    ArityMisTooFew(SrcPos<'s>, usize),
    /// Something was expected (and not found)
    Expected(SrcPos<'s>, &'static str),
    /// Duplicate definition of external variable
    ExtDuplDef(SrcPos<'s>, &'s str),
    /// Undefined constraint
    UndefConstr(SrcPos<'s>, &'s str),
    /// Invalid constraint
    InvalidConstr(SrcPos<'s>),
    /// Invalid type variable
    InvalidTVar(SrcPos<'s>),
    /// Invalid type
    InvalidType(SrcPos<'s>),
    /// Invalid binding pattern
    InvalidBindPatt(SrcPos<'s>),
    /// Invalid top level item
    InvalidTopLevelItem(SrcPos<'s>),
    /// Invalid Algebraic Data Type identifier
    InvalidAdtIdent(SrcPos<'s>, &'s str),
    /// Invalid algebraic data type variant constructor identifier
    InvalidAdtConstrIdent(SrcPos<'s>, &'s str),
    /// Invalid algebraic data type variant
    InvalidAdtVariant(SrcPos<'s>),
    /// Not a special form
    NotASpecForm(SrcPos<'s>, &'s str),
    /// Duplicate definition of algebraic data type
    DataTypeDuplDef {
        pos: SrcPos<'s>,
        name: &'s str,
        prev_pos: SrcPos<'s>,
    },
    /// Undefined type constructor
    UndefTypeCon(SrcPos<'s>, &'s str),
    /// Duplicate definition of a nnnnnvariable
    VarDuplDef {
        pos: SrcPos<'s>,
        name: &'s str,
        prev_pos: SrcPos<'s>,
    },
    /// Duplicate definition of data type constructor
    DataConstrDuplDef {
        pos: SrcPos<'s>,
        name: &'s str,
        prev_pos: SrcPos<'s>,
    },
    UndefDataConstr {
        pos: SrcPos<'s>,
        name: &'s str,
    },
}

impl<'s> PErr<'s> {
    fn code(&self) -> ErrCode {
        fn e(n: usize) -> ErrCode {
            ErrCode {
                module: "parse",
                number: n,
            }
        }
        match *self {
            ArityMis(..) => e(0),
            ArityMisTooFew(..) => e(1),
            Expected(..) => e(2),
            ExtDuplDef(..) => e(3),
            UndefConstr(..) => e(4),
            InvalidConstr(..) => e(5),
            InvalidTVar(..) => e(6),
            InvalidType(..) => e(7),
            InvalidBindPatt(..) => e(8),
            InvalidTopLevelItem(..) => e(9),
            InvalidAdtIdent(..) => e(10),
            InvalidAdtConstrIdent(..) => e(11),
            InvalidAdtVariant(..) => e(12),
            NotASpecForm(..) => e(13),
            DataTypeDuplDef { .. } => e(15),
            UndefTypeCon(..) => e(16),
            VarDuplDef { .. } => e(17),
            DataConstrDuplDef { .. } => e(18),
            UndefDataConstr { .. } => e(19),
        }
    }

    fn write<W: Write>(&self, w: &mut W) {
        let code = self.code();
        match *self {
            ArityMis(ref pos, expected, found) => pos.write_error(
                w,
                code,
                format!("Arity mismatch. Expected {}, found {}", expected, found),
            ),
            ArityMisTooFew(ref pos, found) => pos.write_error(
                w,
                code,
                format!("Arity mismatch. Expected more than {}", found),
            ),
            Expected(ref pos, e) => pos.write_error(w, code, format!("Expected {}", e)),
            ExtDuplDef(ref pos, e) => pos.write_error(
                w,
                code,
                format!("Duplicate declaration of external variable `{}`", e),
            ),
            UndefConstr(ref pos, s) => {
                pos.write_error(w, code, format!("Undefined constraint {}", s))
            }
            InvalidConstr(ref pos) => pos.write_error(w, code, "Invalid constraint"),
            InvalidTVar(ref pos) => pos.write_error(
                w,
                code,
                "Invalid type variable. Type variable must begin with a lower case letter",
            ),
            InvalidType(ref pos) => pos.write_error(w, code, "Invalid type"),
            InvalidBindPatt(ref pos) => pos.write_error(w, code, "Invalid binding pattern"),
            InvalidTopLevelItem(ref pos) => pos.write_error(w, code, "Invalid top level item"),
            InvalidAdtIdent(ref pos, name) => pos.write_error(
                w,
                code,
                format!("Invalid Algebraic Data Type name `{}`", name),
            ),
            InvalidAdtConstrIdent(ref pos, name) => pos.write_error(
                w,
                code,
                format!(
                    "Invalid Algebraic Data Type variant constructor name `{}`",
                    name
                ),
            ),
            InvalidAdtVariant(ref pos) => {
                pos.write_error(w, code, "Invalid Algebraic Data Type variant")
            }
            NotASpecForm(ref pos, s) => {
                pos.write_error(w, code, format!("Not a special form: `{}`", s))
            }
            DataTypeDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => {
                pos.write_error(
                    w,
                    code,
                    format!(
                        "Data type `{}` has already been defined in this scope",
                        name
                    ),
                );
                prev_pos.write_note(w, "The first definition of the data type is here:")
            }
            UndefTypeCon(ref pos, c) => {
                pos.write_error(w, code, format!("Undefined type constructor `{}`", c))
            }
            VarDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => pos.write_error(
                w,
                code,
                format!(
                    "Conflicting definition of variable `{}`\n\
                     Previous definition here `{:?}`",
                    name, prev_pos,
                ),
            ),
            DataConstrDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => {
                pos.write_error(
                    w,
                    code,
                    format!(
                        "Data type constructor `{}` has already been defined in this scope",
                        name
                    ),
                );
                prev_pos.write_note(w, "The previous definition of the constructor is here:")
            }
            UndefDataConstr { ref pos, name } => {
                pos.write_error(w, code, format!("Undefined data constructor `{}`", name));
            }
        }
    }

    fn print(&self) {
        self.write(&mut io::stdout())
    }
}

type PRes<'s, T> = Result<T, PErr<'s>>;

/// A binding pattern
///
/// Patterns are used in variable bindings as a sort of syntax sugar
enum BindPattern<'s> {
    /// Just an identifier
    Var(Ident<'s>),
    /// A function-binding pattern. E.g. `(inc x)`
    Func(Ident<'s>, (Vec<Ident<'s>>, SrcPos<'s>)),
}

// Parser combinators

fn n<'s, 'c>(n_: usize, cs: &'c [Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c [Cst<'s>]> {
    if cs.len() == n_ {
        Ok(cs)
    } else {
        Err(PErr::ArityMis(pos.clone(), n_, cs.len()))
    }
}

fn one<'s, 'c>(cs: &'c [Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c Cst<'s>> {
    n(1, cs, pos).map(|cs| &cs[0])
}

fn two<'s, 'c>(cs: &'c [Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, (&'c Cst<'s>, &'c Cst<'s>)> {
    n(2, cs, pos).map(|cs| (&cs[0], &cs[1]))
}

fn three<'s, 'c>(
    cs: &'c [Cst<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c Cst<'s>, &'c Cst<'s>, &'c Cst<'s>)> {
    n(3, cs, pos).map(|cs| (&cs[0], &cs[1], &cs[2]))
}

fn pair<'s, 'c>(c: &'c Cst<'s>) -> PRes<'s, (&'c Cst<'s>, &'c Cst<'s>)> {
    two(sexpr(c)?, c.pos())
}

fn ident<'s>(c: &Cst<'s>) -> PRes<'s, Ident<'s>> {
    match *c {
        Cst::Ident(s, ref pos) => Ok(Ident {
            s,
            pos: pos.clone(),
        }),
        _ => Err(Expected(c.pos().clone(), "identifier")),
    }
}

fn ident_s<'s, 'c>(c: &'c Cst<'s>) -> PRes<'s, &'s str> {
    ident(c).map(|id| id.s)
}

fn sexpr<'s, 'c>(c: &'c Cst<'s>) -> PRes<'s, &'c [Cst<'s>]> {
    match *c {
        Cst::Sexpr(ref xs, _) => Ok(xs),
        _ => Err(Expected(c.pos().clone(), "sexpr")),
    }
}

fn split_first<'s, 'c>(
    cs: &'c [Cst<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c Cst<'s>, &'c [Cst<'s>])> {
    cs.split_first().ok_or(ArityMisTooFew(pos.clone(), 0))
}

fn split_last<'s, 'c>(
    cs: &'c [Cst<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c Cst<'s>, &'c [Cst<'s>])> {
    cs.split_last().ok_or(ArityMisTooFew(pos.clone(), 0))
}

fn first<'s, 'c>(cs: &'c [Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c Cst<'s>> {
    split_first(cs, pos).map(|(f, _)| f)
}

fn last<'s, 'c>(cs: &'c [Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c Cst<'s>> {
    split_last(cs, pos).map(|(l, _)| l)
}

fn constant<'s, T: Eq>(x: T, y: T, err: PErr<'s>) -> PRes<'s, ()> {
    if x == y {
        Ok(())
    } else {
        Err(err)
    }
}

fn is_special_operator(op: &Cst) -> bool {
    let special_operators = [
        "if", "lambda", "let", ":", "cons", "car", "cdr", "cast", "cond", "new", "match"
    ];
    ident_s(op)
        .map(|s| special_operators.contains(&s))
        .unwrap_or(false)
}

struct Parser<'tvg, 's> {
    /// An additive-only map of module file paths to source code strings
    sources: &'s AddMap<CanonPathBuf, String>,
    /// Counter for generation of unique type variable ids
    type_var_gen: &'tvg mut TypeVarGen,
    /// Algebraic data type definitions
    adts: Adts<'s>,
}

impl<'tvg, 's> Parser<'tvg, 's> {
    fn new(sources: &'s AddMap<CanonPathBuf, String>, type_var_gen: &'tvg mut TypeVarGen) -> Self {
        Parser {
            sources,
            type_var_gen,
            adts: Adts::new(),
        }
    }

    fn gen_tvar(&mut self) -> TVar<'s> {
        TVar::Implicit(self.type_var_gen.gen())
    }

    fn gen_type_var(&mut self) -> Type<'s> {
        Type::Var(self.gen_tvar())
    }

    /// Parse a list of `Cst`s as a module import
    fn parse_import(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, (&'s str, SrcPos<'s>)> {
        let Ident { s, pos } = ident(one(csts, pos)?)?;
        Ok((s, pos.clone()))
    }

    /// Parses a set of import statements
    ///
    /// Returns a map from (modules to import) to
    /// (position of import statement, position of module name)
    fn parse_imports(
        &mut self,
        imports_csts: &[(Vec<Cst<'s>>, &SrcPos<'s>)],
    ) -> PRes<'s, BTreeMap<&'s str, (SrcPos<'s>, SrcPos<'s>)>> {
        let mut imports = BTreeMap::new();
        for &(ref import_csts, pos) in imports_csts {
            let (module_name, name_pos) = self.parse_import(import_csts, pos)?;
            if let Some((prev_pos, _)) = imports.insert(module_name, (pos.clone(), name_pos)) {
                pos.print_warn(format!("Duplicate import of module `{}`", module_name));
                prev_pos.print_note(format!("Previous import of module `{}` here", module_name));
            }
        }
        Ok(imports)
    }

    /// Parse a list of `Cst`s as an external variable declaration
    fn parse_extern(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, ExternDecl<'s>> {
        let (a, b) = two(csts, pos)?;
        Ok(ExternDecl {
            ident: ident(a)?,
            typ: self.parse_type(b)?,
            pos: pos.clone(),
        })
    }

    fn parse_externs(
        &mut self,
        decls_csts: &[(Vec<Cst<'s>>, SrcPos<'s>)],
    ) -> PRes<'s, BTreeMap<&'s str, ExternDecl<'s>>> {
        let mut externs = BTreeMap::new();
        for &(ref decl_csts, ref pos) in decls_csts {
            let ext = self.parse_extern(decl_csts, pos)?;
            if let Some(ext) = externs.insert(ext.ident.s, ext) {
                return Err(ExtDuplDef(ext.pos.clone(), ext.ident.s));
            }
        }
        Ok(externs)
    }

    fn parse_type_var_ident(&mut self, cst: &Cst<'s>) -> PRes<'s, Ident<'s>> {
        let id = ident(cst)?;
        if id.s.starts_with(char::is_lowercase) {
            Ok(id)
        } else {
            Err(InvalidTVar(id.pos))
        }
    }

    fn parse_type_var(&mut self, cst: &Cst<'s>) -> PRes<'s, TVar<'s>> {
        self.parse_type_var_ident(cst)
            .map(|id| TVar::Explicit(id.s))
    }

    fn parse_constraint_class(&mut self, cst: &Cst<'s>) -> PRes<'s, &'s str> {
        match *cst {
            Cst::Ident("Num", _) => Ok("Num"),
            Cst::Ident(s, ref pos) => Err(UndefConstr(pos.clone(), s)),
            _ => Err(InvalidConstr(cst.pos().clone())),
        }
    }

    fn parse_constraints(
        &mut self,
        csts: &[Cst<'s>],
    ) -> PRes<'s, BTreeMap<TVar<'s>, BTreeSet<&'s str>>> {
        let mut constrs = BTreeMap::new();
        for cst in csts {
            let (a, b) = pair(cst)?;
            let class = self.parse_constraint_class(a)?;
            let tv = self.parse_type_var(b)?;
            constrs.entry(tv).or_insert(BTreeSet::new()).insert(class);
        }
        Ok(constrs)
    }

    /// Parse a definition of constraints
    fn parse_constrained_type(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Poly<'s>> {
        let (a, b) = two(csts, pos)?;
        let cs = sexpr(a)?;
        let params = self.parse_constraints(cs)?;
        let body = self.parse_type(b)?;
        Ok(Poly { params, body })
    }

    fn parse_def_type_sig_sexpr(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Poly<'s>> {
        let is_constrain = csts.first()
            .and_then(|c| ident_s(c).ok().map(|s| s == "constrain"))
            .unwrap_or(false);
        if is_constrain {
            self.parse_constrained_type(&csts[1..], pos)
        } else {
            Ok(Poly {
                params: BTreeMap::new(),
                body: self.parse_type_sexpr(csts, pos)?,
            })
        }
    }

    fn parse_def_type_sig(&mut self, cst: &Cst<'s>) -> PRes<'s, Poly<'s>> {
        match *cst {
            Cst::Sexpr(ref app, ref pos) => self.parse_def_type_sig_sexpr(app, pos),
            _ => Ok(Poly {
                params: BTreeMap::new(),
                body: self.parse_type(cst)?,
            }),
        }
    }

    fn parse_func_type(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Type<'s>> {
        let (ret, init) = split_last(csts, pos)?;
        let (last_param, init_params) = split_last(init, pos)?;
        let last_fn = Type::new_func(self.parse_type(last_param)?, self.parse_type(ret)?);
        init_params.iter().rev().fold(Ok(last_fn), |acc, t| {
            Ok(Type::new_func(self.parse_type(t)?, acc?))
        })
    }

    fn parse_cons_type(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Type<'s>> {
        let (a, b) = two(csts, pos)?;
        let car = self.parse_type(a)?;
        let cdr = self.parse_type(b)?;
        Ok(Type::new_cons(car, cdr))
    }

    fn parse_ptr_type(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Type<'s>> {
        self.parse_type(one(csts, pos)?).map(Type::new_ptr)
    }

    fn parse_type_sexpr(&mut self, app: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Type<'s>> {
        let (first, rest) = split_first(app, pos)?;
        let id = ident(first)?;
        let (s, p) = (id.s, id.pos);
        match s {
            "->" => self.parse_func_type(rest, pos),
            "Cons" => self.parse_cons_type(rest, pos),
            "Ptr" => self.parse_ptr_type(rest, pos),
            _ => Err(UndefTypeCon(p.clone(), s)),
        }
    }

    fn parse_type_ident(&mut self, id: &'s str, pos: &SrcPos<'s>) -> PRes<'s, Type<'s>> {
        match id {
            "_" => Ok(self.gen_type_var()),
            "Nil" => Ok(TYPE_NIL.clone()),
            // The type identifier starts with a lowercase letter => Is a type variable
            s if s.starts_with(char::is_lowercase) => Ok(Type::Var(TVar::Explicit(s))),
            // Doesn't start with lowercase => Is a type constant e.g. Int32
            s => Ok(Type::Const(s, Some(pos.clone()))),
        }
    }

    /// Parse a syntax tree as a `Type`
    fn parse_type(&mut self, tree: &Cst<'s>) -> PRes<'s, Type<'s>> {
        let t = match *tree {
            Cst::Sexpr(ref sexp, ref pos) => self.parse_type_sexpr(sexp, pos),
            Cst::Ident(s, ref pos) => self.parse_type_ident(s, &pos),
            _ => Err(InvalidType(tree.pos().clone())),
        };
        t.map(|t| t.canonicalize())
    }

    fn parse_app_bind_pattern(
        &mut self,
        app: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, BindPattern<'s>> {
        let (fst, rest) = split_first(app, pos)?;
        let f_id = ident(fst)?;
        let first_param = first(rest, pos)?;
        let last_param = last(rest, pos)?;
        let params_pos = first_param.pos().to(last_param.pos());
        let params_ids = rest.iter().map(|a| ident(a)).collect::<PRes<Vec<_>>>()?;
        Ok(BindPattern::Func(f_id, (params_ids, params_pos)))
    }

    /// Parse a syntax tree as a BindPattern
    fn parse_bind_pattern(&mut self, cst: &Cst<'s>) -> PRes<'s, BindPattern<'s>> {
        match *cst {
            Cst::Ident(s, ref pos) => Ok(BindPattern::Var(Ident {
                s,
                pos: pos.clone(),
            })),
            Cst::Sexpr(ref app, ref pos) => self.parse_app_bind_pattern(app, pos),
            _ => Err(InvalidBindPatt(cst.pos().clone())),
        }
    }

    fn new_multary_app(
        &mut self,
        func: Expr<'s>,
        args: &[Expr<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, App<'s>> {
        let (last, init) = args.split_last().ok_or(ArityMisTooFew(pos.clone(), 0))?;
        let apps = init.iter().fold(func, |f, arg| {
            Expr::App(Box::new(App {
                func: f,
                arg: arg.clone(),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            }))
        });
        Ok(App {
            func: apps,
            arg: last.clone(),
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    /// Parse a first `Cst` and some following `Cst`s as a procedure and some arguments,
    /// i.e. a function application
    fn parse_app(
        &mut self,
        func_cst: &Cst<'s>,
        args_csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, App<'s>> {
        let func = self.parse_expr(func_cst)?;
        let args = args_csts
            .iter()
            .map(|a| self.parse_expr(a))
            .collect::<PRes<Vec<_>>>()?;
        self.new_multary_app(func, &args, &pos)
    }

    /// Parse a list of `Cst`s as parts of an `If` conditional
    fn parse_if(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, If<'s>> {
        let (p, c, a) = three(csts, args_pos)?;
        Ok(If {
            predicate: self.parse_expr(p)?,
            consequent: self.parse_expr(c)?,
            alternative: self.parse_expr(a)?,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    /// Parse the `else` clause of a `cond`
    fn parse_else_clause(&mut self, cst: &Cst<'s>) -> PRes<'s, Expr<'s>> {
        let (pred, conseq) = pair(cst)?;
        constant(ident_s(pred)?, "else", Expected(pred.pos().clone(), "else"))
            .and_then(|_| self.parse_expr(conseq))
    }

    /// Parse a clause of a `cond`
    fn parse_cond_clause(&mut self, cst: &Cst<'s>) -> PRes<'s, (Expr<'s>, Expr<'s>)> {
        let (p, c) = pair(cst)?;
        Ok((self.parse_expr(p)?, self.parse_expr(c)?))
    }

    /// Parse a sequence of token trees as the clauses of a `cond` special form
    ///
    /// Translate to nested `If`s
    fn parse_cond(&mut self, csts: &[Cst<'s>], args_pos: &SrcPos<'s>) -> PRes<'s, Expr<'s>> {
        let (last, init) = split_last(csts, args_pos)?;
        let else_val = self.parse_else_clause(last);
        init.iter().rev().fold(else_val, |alternative, c| {
            let (predicate, consequent) = self.parse_cond_clause(c)?;
            Ok(Expr::If(box If {
                predicate,
                consequent,
                alternative: alternative?,
                pos: c.pos().clone(),
                typ: self.gen_type_var(),
            }))
        })
    }

    fn new_multary_lambda(
        &mut self,
        params: &[(Ident<'s>, Type<'s>)],
        params_pos: &SrcPos<'s>,
        body: Expr<'s>,
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Lambda<'s>> {
        let (last, init) = params
            .split_last()
            .ok_or(ArityMisTooFew(params_pos.clone(), 0))?;
        let innermost = Lambda {
            param_ident: last.0.clone(),
            body: body,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        };
        Ok(init.iter()
            .rev()
            .cloned()
            .fold(innermost, |inner, param| Lambda {
                param_ident: param.0,
                body: Expr::Lambda(Box::new(inner)),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            }))
    }

    /// Parse a list of `Cst`s as the parts of a `Lambda`
    fn parse_lambda(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Lambda<'s>> {
        let (a, b) = two(csts, args_pos)?;
        let params_csts = sexpr(a)?;
        let params_pos = a.pos();
        let params = params_csts
            .iter()
            .map(|p| Ok((ident(p)?, self.gen_type_var())))
            .collect::<PRes<Vec<_>>>()?;
        let body = self.parse_expr(b)?;
        self.new_multary_lambda(&params, params_pos, body, pos)
    }

    fn parse_binding(
        &mut self,
        patt: &Cst<'s>,
        maybe_sig: Option<&Cst<'s>>,
        val: &Cst<'s>,
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Binding<'s>> {
        let sig = maybe_sig
            .map(|c| self.parse_def_type_sig(c))
            .unwrap_or_else(|| {
                Ok(Poly {
                    params: BTreeMap::new(),
                    body: self.gen_type_var(),
                })
            })?;
        Ok(match self.parse_bind_pattern(patt)? {
            BindPattern::Var(ident) => Binding {
                ident,
                sig,
                val: self.parse_expr(val)?,
                mono_insts: BTreeMap::new(),
                pos: pos.clone(),
            },
            BindPattern::Func(f_id, (params_ids, params_pos)) => {
                let params = params_ids
                    .into_iter()
                    .map(|id| (id, self.gen_type_var()))
                    .collect::<Vec<_>>();
                let body = self.parse_expr(val)?;
                Binding {
                    ident: f_id,
                    sig: sig,
                    val: Expr::Lambda(Box::new(self.new_multary_lambda(
                        &params,
                        &params_pos,
                        body,
                        pos,
                    )?)),
                    mono_insts: BTreeMap::new(),
                    pos: pos.clone(),
                }
            }
        })
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
    fn parse_untyped_binding(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Binding<'s>> {
        let (patt, val) = two(csts, pos)?;
        self.parse_binding(patt, None, val, pos)
    }

    fn parse_typed_binding(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Binding<'s>> {
        let (patt, typ, val) = three(csts, pos)?;
        self.parse_binding(patt, Some(typ), val, pos)
    }

    fn parse_bindings_to_flat_map(
        &mut self,
        defs: &[(bool, &[Cst<'s>], SrcPos<'s>)],
    ) -> PRes<'s, BTreeMap<&'s str, Binding<'s>>> {
        let mut bindings = BTreeMap::new();
        for &(is_typed, ref def_csts, ref pos) in defs {
            let binding = if is_typed {
                self.parse_typed_binding(def_csts, pos)?
            } else {
                self.parse_untyped_binding(def_csts, pos)?
            };
            let (name, pos) = (binding.ident.s, binding.pos.clone());
            if let Some(prev_binding) = bindings.insert(name, binding) {
                return Err(VarDuplDef {
                    name,
                    pos,
                    prev_pos: prev_binding.pos,
                });
            }
        }
        Ok(bindings)
    }

    fn parse_bindings(
        &mut self,
        defs: &[(bool, &[Cst<'s>], SrcPos<'s>)],
    ) -> PRes<'s, TopologicallyOrderedDependencyGroups<'s>> {
        self.parse_bindings_to_flat_map(defs)
            .map(flat_bindings_to_topologically_ordered)
    }

    fn parse_let_bindings(
        &mut self,
        csts: &[Cst<'s>],
    ) -> PRes<'s, TopologicallyOrderedDependencyGroups<'s>> {
        let mut bindings_csts = Vec::new();
        for cst in csts {
            let binding_pair = sexpr(cst)?;
            bindings_csts.push((false, binding_pair.clone(), cst.pos().clone()))
        }
        self.parse_bindings(&bindings_csts)
    }

    /// Parse a `let` special form and return as an invocation of a lambda
    fn parse_let(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Let<'s>> {
        let (a, b) = two(csts, args_pos)?;
        let binds_csts = sexpr(a)?;
        Ok(Let {
            bindings: self.parse_let_bindings(binds_csts)?,
            body: self.parse_expr(b)?,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    /// Parse a list of `Cst`s as a `TypeAscript`
    fn parse_type_ascript(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, TypeAscript<'s>> {
        let (a, b) = two(csts, args_pos)?;
        Ok(TypeAscript {
            typ: self.parse_type(b)?,
            expr: self.parse_expr(a)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `Cst`s as a `Cons` pair
    fn parse_cons(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Cons<'s>> {
        let (a, b) = two(csts, args_pos)?;
        Ok(Cons {
            typ: self.gen_type_var(),
            car: self.parse_expr(a)?,
            cdr: self.parse_expr(b)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `Cst`s as a `car` operation
    fn parse_car(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Car<'s>> {
        Ok(Car {
            typ: self.gen_type_var(),
            expr: self.parse_expr(one(csts, args_pos)?)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `Cst`s as a `cdr` operation
    fn parse_cdr(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Cdr<'s>> {
        Ok(Cdr {
            typ: self.gen_type_var(),
            expr: self.parse_expr(one(csts, args_pos)?)?,
            pos: pos.clone(),
        })
    }

    /// Parse a type cast
    ///
    /// `(cast VAL TYPE)`, e.g. `(cast (: 1 Int32) Int64)`
    fn parse_cast(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Cast<'s>> {
        let (a, b) = two(csts, args_pos)?;
        Ok(Cast {
            expr: self.parse_expr(a)?,
            typ: self.parse_type(b)?,
            pos: pos.clone(),
        })
    }

    fn parse_variant(&mut self, cst: &Cst<'s>) -> PRes<'s, Ident<'s>> {
        let constr = ident(cst)?;
        if self.adts.variant_exists(constr.s) {
            Ok(constr)
        } else {
            Err(UndefDataConstr {
                pos: constr.pos,
                name: constr.s,
            })
        }
    }

    fn parse_new(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, New<'s>> {
        let (first, rest) = split_first(csts, args_pos)?;
        let constr = self.parse_variant(first)?;
        let members = rest.iter()
            .map(|c| self.parse_expr(c))
            .collect::<PRes<_>>()?;
        Ok(New {
            constr,
            members,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    fn parse_deconstr_pattern(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Deconstr<'s>> {
        let (head, tail) = split_first(csts, pos)?;
        let constr = self.parse_variant(head)?;
        let subpatts = tail.iter()
            .map(|c| self.parse_pattern(c))
            .collect::<PRes<_>>()?;
        Ok(Deconstr {
            constr,
            subpatts,
            pos: pos.clone(),
        })
    }

    fn parse_pattern(&mut self, cst: &Cst<'s>) -> PRes<'s, Pattern<'s>> {
        match *cst {
            Cst::Sexpr(ref sexpr, ref pos) => self.parse_deconstr_pattern(sexpr, pos)
                .map(|d| Pattern::Deconstr(box d)),
            Cst::Ident("nil", ref pos) => Ok(Pattern::Nil(Nil { pos: pos.clone() })),
            Cst::Ident(ident, ref pos) if self.adts.variant_exists(ident) => {
                Ok(Pattern::Deconstr(box Deconstr {
                    constr: Ident::new(ident, pos.clone()),
                    subpatts: vec![],
                    pos: pos.clone(),
                }))
            }
            Cst::Ident(ident, ref pos) => Ok(Pattern::Variable(Variable {
                ident: Ident::new(ident, pos.clone()),
                typ: self.gen_type_var(),
            })),
            Cst::Num(num, ref pos) => Ok(Pattern::NumLit(NumLit {
                lit: num,
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
            Cst::Str(ref s, ref pos) => Ok(Pattern::StrLit(StrLit {
                lit: s.clone(),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
        }
    }

    fn parse_case(&mut self, cst: &Cst<'s>) -> PRes<'s, Case<'s>> {
        let (patt_cst, body_cst) = pair(cst)?;
        Ok(Case {
            patt: self.parse_pattern(patt_cst)?,
            patt_typ: self.gen_type_var(),
            body: self.parse_expr(body_cst)?,
            pos: cst.pos().clone(),
        })
    }

    fn parse_cases(&mut self, csts: &[Cst<'s>]) -> PRes<'s, Vec<Case<'s>>> {
        csts.iter().map(|c| self.parse_case(c)).collect()
    }

    fn parse_match(
        &mut self,
        csts: &[Cst<'s>],
        pos: &SrcPos<'s>,
        args_pos: &SrcPos<'s>,
    ) -> PRes<'s, Match<'s>> {
        let (first, rest) = split_first(csts, args_pos)?;
        Ok(Match {
            expr: self.parse_expr(first)?,
            cases: self.parse_cases(rest)?,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    fn parse_special_form(
        &mut self,
        head: &Cst<'s>,
        tail: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Expr<'s>> {
        let form = ident(head)?;
        let tail_pos = pos.after(&form.pos);
        match form.s {
            "if" => Ok(Expr::If(Box::new(self.parse_if(tail, pos, &tail_pos)?))),
            "lambda" => Ok(Expr::Lambda(Box::new(self.parse_lambda(
                tail,
                pos,
                &tail_pos,
            )?))),
            "let" => Ok(Expr::Let(Box::new(self.parse_let(tail, pos, &tail_pos)?))),
            ":" => Ok(Expr::TypeAscript(Box::new(self.parse_type_ascript(
                tail,
                pos,
                &tail_pos,
            )?))),
            "cons" => Ok(Expr::Cons(Box::new(self.parse_cons(tail, pos, &tail_pos)?))),
            "car" => Ok(Expr::Car(Box::new(self.parse_car(tail, pos, &tail_pos)?))),
            "cdr" => Ok(Expr::Cdr(Box::new(self.parse_cdr(tail, pos, &tail_pos)?))),
            "cast" => Ok(Expr::Cast(Box::new(self.parse_cast(tail, pos, &tail_pos)?))),
            "new" => Ok(Expr::New(Box::new(self.parse_new(tail, pos, &tail_pos)?))),
            "match" => Ok(Expr::Match(Box::new(self.parse_match(
                tail,
                pos,
                &tail_pos,
            )?))),

            // "Macros"
            "cond" => self.parse_cond(tail, &tail_pos),
            _ => Err(NotASpecForm(form.pos.clone(), form.s)),
        }
    }

    /// Parse a sexpr as an expr
    fn parse_sexpr_expr(&mut self, cs: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, Expr<'s>> {
        if let Some((head, tail)) = cs.split_first() {
            if is_special_operator(head) {
                self.parse_special_form(head, tail, pos)
            } else {
                self.parse_app(head, tail, pos).map(|a| Expr::App(box a))
            }
        } else {
            Ok(Expr::Nil(Nil { pos: pos.clone() }))
        }
    }

    /// Parse a `Cst` as an `Expr`
    fn parse_expr(&mut self, cst: &Cst<'s>) -> PRes<'s, Expr<'s>> {
        match *cst {
            Cst::Sexpr(ref sexpr, ref pos) => self.parse_sexpr_expr(sexpr, pos),
            Cst::Ident("nil", ref pos) => Ok(Expr::Nil(Nil { pos: pos.clone() })),
            Cst::Ident("true", ref pos) => Ok(Expr::Bool(Bool {
                val: true,
                pos: pos.clone(),
            })),
            Cst::Ident("false", ref pos) => Ok(Expr::Bool(Bool {
                val: false,
                pos: pos.clone(),
            })),
            Cst::Ident(ident, ref pos) => Ok(Expr::Variable(Variable {
                ident: Ident::new(ident, pos.clone()),
                typ: self.gen_type_var(),
            })),
            Cst::Num(num, ref pos) => Ok(Expr::NumLit(NumLit {
                lit: num,
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
            Cst::Str(ref s, ref pos) => Ok(Expr::StrLit(StrLit {
                lit: s.clone(),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
        }
    }

    /// Parse the members of an algebraic data type variant
    fn parse_data_type_variant_members(
        &mut self,
        cs: &[Cst<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Vec<Type<'s>>> {
        first(cs, pos)?;
        cs.iter().map(|c| self.parse_type(c)).collect()
    }

    /// Parse a variant of a data type definition
    fn parse_data_type_variant(&mut self, c: &Cst<'s>) -> PRes<'s, AdtVariant<'s>> {
        match *c {
            Cst::Ident(s, ref p) => Ok(AdtVariant {
                name: Ident {
                    s: s,
                    pos: p.clone(),
                },
                members: vec![],
                pos: p.clone(),
            }),
            Cst::Sexpr(ref cs, ref p) => {
                let (name_c, members_cs) = split_first(cs, p)?;
                let name = ident(name_c)?;
                if !name.s.starts_with(char::is_uppercase) {
                    return Err(InvalidAdtConstrIdent(name.pos, name.s));
                }
                let name_pos = name.pos.clone();
                Ok(AdtVariant {
                    name: name,
                    members: self.parse_data_type_variant_members(members_cs, &p.after(&name_pos))?,
                    pos: p.clone(),
                })
            }
            _ => Err(InvalidAdtVariant(c.pos().clone())),
        }
    }

    /// Parse a list of variants of a data type definition
    fn parse_data_type_variants(&mut self, cs: &[Cst<'s>]) -> PRes<'s, Vec<AdtVariant<'s>>> {
        cs.iter().map(|c| self.parse_data_type_variant(c)).collect()
    }

    /// Parse a data type definition
    fn parse_data_type_def(&mut self, csts: &[Cst<'s>], pos: &SrcPos<'s>) -> PRes<'s, AdtDef<'s>> {
        let (name_c, variants_c) = split_first(csts, pos)?;
        let name = ident(name_c)?;
        if !name.s.starts_with(char::is_uppercase) {
            return Err(InvalidAdtIdent(name.pos.clone(), name.s));
        }
        Ok(AdtDef {
            name,
            variants: self.parse_data_type_variants(variants_c)?,
            pos: pos.clone(),
        })
    }

    fn parse_data_type_defs(&mut self, defs_csts: &[(Vec<Cst<'s>>, SrcPos<'s>)]) -> PRes<'s, ()> {
        for &(ref def_csts, ref pos) in defs_csts {
            let def = self.parse_data_type_def(def_csts, pos)?;
            if let Some(prev_def) = self.adts.defs.insert(def.name.s, def.clone()) {
                return Err(DataTypeDuplDef {
                    pos: def.pos,
                    name: prev_def.name.s,
                    prev_pos: prev_def.pos.clone(),
                });
            }
            for variant in &def.variants {
                if !self.adts.variants.contains_key(variant.name.s) {
                    self.adts.variants.insert(variant.name.s, def.name.s);
                } else {
                    return Err(DataConstrDuplDef {
                        pos: variant.pos.clone(),
                        name: variant.name.s,
                        prev_pos: self.adts
                            .adt_variant_of_name(variant.name.s)
                            .expect("ICE: No adt_variant_of_name")
                            .pos
                            .clone(),
                    });
                }
            }
        }
        Ok(())
    }

    fn _get_top_level_csts<'c>(
        &mut self,
        csts: &'c [Cst<'s>],
        externs: &mut Vec<(Vec<Cst<'s>>, SrcPos<'s>)>,
        globals: &mut Vec<(bool, Vec<Cst<'s>>, SrcPos<'s>)>,
        adts: &mut Vec<(Vec<Cst<'s>>, SrcPos<'s>)>,
    ) -> PRes<'s, ()> {
        let mut imports_csts = Vec::new();
        for cst in csts {
            let pos = cst.pos();
            let (first, rest) = split_first(sexpr(cst)?, cst.pos())?;
            let first_s = ident_s(first)?;
            match first_s {
                "import" => imports_csts.push((rest.to_vec(), pos)),
                "extern" => externs.push((rest.to_vec(), pos.clone())),
                "define" => globals.push((false, rest.to_vec(), pos.clone())),
                "define:" => globals.push((true, rest.to_vec(), pos.clone())),
                "data" => adts.push((rest.to_vec(), pos.clone())),
                _ => return Err(InvalidTopLevelItem(pos.clone())),
            }
        }
        let imports = self.parse_imports(&imports_csts)?;
        // Recursively get top level csts of imported modules as well
        for (module_name, (_, _)) in imports {
            let module_path = CanonPathBuf::new(&format!("{}.kvs", module_name))
                .expect("ICE: Failed to canonicalize module path");
            if !self.sources.contains_key(&module_path) {
                let import_csts = lex_file(module_path, &self.sources);
                self._get_top_level_csts(&import_csts, externs, globals, adts)?
            }
        }
        Ok(())
    }

    /// Separate `csts` into token trees for externs, and globals
    ///
    /// Recursively follow imports and get top level csts from there as well
    fn get_top_level_csts<'c>(
        &mut self,
        csts: &'c [Cst<'s>],
    ) -> PRes<
        's,
        (
            Vec<(Vec<Cst<'s>>, SrcPos<'s>)>,
            Vec<(bool, Vec<Cst<'s>>, SrcPos<'s>)>,
            Vec<(Vec<Cst<'s>>, SrcPos<'s>)>,
        ),
    > {
        let (mut externs, mut globals, mut adts) = (Vec::new(), Vec::new(), Vec::new());
        self._get_top_level_csts(csts, &mut externs, &mut globals, &mut adts)?;
        Ok((externs, globals, adts))
    }

    fn parse_ast(&mut self, csts: &[Cst<'s>]) -> PRes<'s, Ast<'s>> {
        let (externs_csts, globals_csts, adts_csts) = self.get_top_level_csts(csts)?;
        let globals_csts_slc = globals_csts
            .iter()
            .map(|&(is_typed, ref v, ref p)| (is_typed, v.as_slice(), p.clone()))
            .collect::<Vec<_>>();
        self.parse_data_type_defs(&adts_csts)?;
        let externs = self.parse_externs(&externs_csts)?;
        let globals = self.parse_bindings(&globals_csts_slc)?;
        Ok(Ast {
            externs,
            globals,
            adts: mem::replace(&mut self.adts, Adts::new()),
        })
    }

    /// Parse the file `filename`, and recursively parse imports as well
    fn parse_file(&mut self, filename: CanonPathBuf) -> PRes<'s, Ast<'s>> {
        let csts = lex_file(filename, &self.sources);
        self.parse_ast(&csts)
    }
}

/// Returns the Abstract Syntax Tree of the program with entry point in `filename`
///
/// Given the name of a file that contains the program entry point,
/// read, lex, and parse the source, and include imported modules
/// as needed
pub fn parse_program<'s>(
    filename: CanonPathBuf,
    sources: &'s AddMap<CanonPathBuf, String>,
    type_var_gen: &mut TypeVarGen,
) -> Ast<'s> {
    let mut parser = Parser::new(sources, type_var_gen);
    parser.parse_file(filename).unwrap_or_else(|e| {
        e.print();
        exit()
    })
}

// TODO: Fix all passings of `pos` to functions like `first`, `split_first`, `two`, etc.
//       Many are wrong!

#[cfg(test)]
mod test {
    use lib::collections::AddMap;
    use lib::front::lex::Cst;
    use lib::front::*;
    use lib::front::ast::*;
    use super::Parser;

    fn dummy_cident(s: &str) -> Cst {
        Cst::Ident(s, SrcPos::new_dummy())
    }

    fn dummy_ident(s: &str) -> Ident {
        Ident {
            s,
            pos: SrcPos::new_dummy(),
        }
    }

    #[test]
    fn test_parse_data_type_def() {
        let sources = AddMap::new();
        let mut tvg = TypeVarGen::new(0);
        let mut parser = Parser::new(&sources, &mut tvg);
        assert_eq!(
            parser.parse_data_type_def(
                &[dummy_cident("Foo"), dummy_cident("Foo"),],
                &SrcPos::new_dummy()
            ),
            Ok(AdtDef {
                name: Ident {
                    s: "Foo",
                    pos: SrcPos::new_dummy(),
                },
                variants: vec![
                    AdtVariant {
                        name: dummy_ident("Foo"),
                        members: vec![],
                        pos: SrcPos::new_dummy(),
                    },
                ],
                pos: SrcPos::new_dummy(),
            })
        )
    }
}
