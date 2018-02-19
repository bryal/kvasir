use self::PErr::*;
use super::*;
use super::ast::*;
use super::lex::CST;
use super::dependency_graph::*;
use lib::CanonPathBuf;
use lib::collections::AddMap;
use lib::front::lex::lex_file;
use std::collections::BTreeMap;

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
    /// Invalid pattern
    InvalidPatt(SrcPos<'s>),
    /// Invalid top level item
    InvalidTopLevelItem(SrcPos<'s>),
    /// Invalid Algebraic Data Type identifier
    InvalidAdtIdent(SrcPos<'s>, &'s str),
    /// Invalid algebraic data type variant constructor identifier
    InvalidAdtConstrIdent(SrcPos<'s>, &'s str),
    /// Invalid algebraic data type variant
    InvalidAdtVariant(SrcPos<'s>),
    /// Duplicate constraints definition for type variable
    TVarDuplDef {
        pos: SrcPos<'s>,
        name: &'s str,
        prev_pos: SrcPos<'s>,
    },
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
}

impl<'s> PErr<'s> {
    fn write<W: Write>(&self, w: &mut W) {
        match *self {
            ArityMis(ref pos, expected, found) => pos.write_error(
                w,
                format!("Arity mismatch. Expected {}, found {}", expected, found),
            ),
            ArityMisTooFew(ref pos, found) => {
                pos.write_error(w, format!("Arity mismatch. Expected more than {}", found))
            }
            Expected(ref pos, e) => pos.write_error(w, format!("Expected {}", e)),
            ExtDuplDef(ref pos, e) => pos.write_error(
                w,
                format!("Duplicate declaration of external variable `{}`", e),
            ),
            UndefConstr(ref pos, s) => pos.write_error(w, format!("Undefined constraint {}", s)),
            InvalidConstr(ref pos) => pos.write_error(w, "Invalid constraint"),
            InvalidTVar(ref pos) => pos.write_error(
                w,
                "Invalid type variable. Type variable must begin with a lower case letter",
            ),
            InvalidType(ref pos) => pos.write_error(w, "Invalid type"),
            InvalidPatt(ref pos) => pos.write_error(w, "Invalid pattern"),
            InvalidTopLevelItem(ref pos) => pos.write_error(w, "Invalid top level item"),
            InvalidAdtIdent(ref pos, name) => {
                pos.write_error(w, format!("Invalid Algebraic Data Type name `{}`", name))
            }
            InvalidAdtConstrIdent(ref pos, name) => pos.write_error(
                w,
                format!(
                    "Invalid Algebraic Data Type variant constructor name `{}`",
                    name
                ),
            ),
            InvalidAdtVariant(ref pos) => pos.write_error(w, "Invalid Algebraic Data Type variant"),
            TVarDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => {
                pos.write_error(
                    w,
                    format!(
                        "Type variable `{}` has already been defined in this scope",
                        name
                    ),
                );
                prev_pos.write_note(
                    w,
                    "A type variable is implicitly defined the first time it is used \
                     in a scope.\nTry removing the constraints of this instance of \
                     the type variable, \nand add them to the first instance instead.\n\
                     The first instance of the type variable is here:",
                )
            }
            DataTypeDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => {
                pos.write_error(
                    w,
                    format!(
                        "Data type `{}` has already been defined in this scope",
                        name
                    ),
                );
                prev_pos.write_note(w, "The first definition of the data type is here:")
            }
            UndefTypeCon(ref pos, c) => {
                pos.write_error(w, format!("Undefined type constructor `{}`", c))
            }
            VarDuplDef {
                ref pos,
                name,
                ref prev_pos,
            } => pos.write_error(
                w,
                format!(
                    "Conflicting definition of variable `{}`\n\
                     Previous definition here `{:?}`",
                    name, prev_pos,
                ),
            ),
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
enum Pattern<'s> {
    /// Just an identifier
    Var(Ident<'s>),
    /// A function-binding pattern. E.g. `(inc x)`
    Func(Ident<'s>, (Vec<Ident<'s>>, SrcPos<'s>)),
}

// Parser combinators

fn n<'s, 'c>(n_: usize, cs: &'c [CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c [CST<'s>]> {
    if cs.len() == n_ {
        Ok(cs)
    } else {
        Err(PErr::ArityMis(pos.clone(), n_, cs.len()))
    }
}

fn one<'s, 'c>(cs: &'c [CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c CST<'s>> {
    n(1, cs, pos).map(|cs| &cs[0])
}

fn two<'s, 'c>(cs: &'c [CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, (&'c CST<'s>, &'c CST<'s>)> {
    n(2, cs, pos).map(|cs| (&cs[0], &cs[1]))
}

fn three<'s, 'c>(
    cs: &'c [CST<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c CST<'s>, &'c CST<'s>, &'c CST<'s>)> {
    n(3, cs, pos).map(|cs| (&cs[0], &cs[1], &cs[2]))
}

fn pair<'s, 'c>(c: &'c CST<'s>) -> PRes<'s, (&'c CST<'s>, &'c CST<'s>)> {
    two(sexpr(c)?, c.pos())
}

fn ident<'s>(c: &CST<'s>) -> PRes<'s, Ident<'s>> {
    match *c {
        CST::Ident(s, ref pos) => Ok(Ident {
            s,
            pos: pos.clone(),
        }),
        _ => Err(Expected(c.pos().clone(), "identifier")),
    }
}

fn ident_s<'s, 'c>(c: &'c CST<'s>) -> PRes<'s, &'s str> {
    ident(c).map(|id| id.s)
}

fn sexpr<'s, 'c>(c: &'c CST<'s>) -> PRes<'s, &'c [CST<'s>]> {
    match *c {
        CST::SExpr(ref xs, _) => Ok(xs),
        _ => Err(Expected(c.pos().clone(), "sexpr")),
    }
}

fn split_first<'s, 'c>(
    cs: &'c [CST<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c CST<'s>, &'c [CST<'s>])> {
    cs.split_first().ok_or(ArityMisTooFew(pos.clone(), 0))
}

fn split_last<'s, 'c>(
    cs: &'c [CST<'s>],
    pos: &SrcPos<'s>,
) -> PRes<'s, (&'c CST<'s>, &'c [CST<'s>])> {
    cs.split_last().ok_or(ArityMisTooFew(pos.clone(), 0))
}

fn first<'s, 'c>(cs: &'c [CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c CST<'s>> {
    split_first(cs, pos).map(|(f, _)| f)
}

fn last<'s, 'c>(cs: &'c [CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, &'c CST<'s>> {
    split_last(cs, pos).map(|(l, _)| l)
}

fn constant<'s, T: Eq>(x: T, y: T, err: PErr<'s>) -> PRes<'s, ()> {
    if x == y {
        Ok(())
    } else {
        Err(err)
    }
}

struct Parser<'tvg, 's> {
    /// An additive-only map of module file paths to source code strings
    sources: &'s AddMap<CanonPathBuf, String>,
    /// Counter for generation of unique type variable ids
    type_var_gen: &'tvg mut TypeVarGen,
}

impl<'tvg, 's> Parser<'tvg, 's> {
    fn new(sources: &'s AddMap<CanonPathBuf, String>, type_var_gen: &'tvg mut TypeVarGen) -> Self {
        Parser {
            sources,
            type_var_gen,
        }
    }

    fn gen_tvar(&mut self) -> TVar<'s> {
        TVar {
            id: self.type_var_gen.gen(),
            constrs: BTreeSet::new(),
            explicit: None,
        }
    }

    fn gen_type_var(&mut self) -> Type<'s> {
        Type::Var(self.gen_tvar())
    }

    /// Parse a list of `CST`s as a module import
    fn parse_import(
        &mut self,
        csts: &[CST<'s>],
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
        imports_csts: &[(Vec<CST<'s>>, &SrcPos<'s>)],
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

    /// Parse a list of `CST`s as an external variable declaration
    fn parse_extern(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, ExternDecl<'s>> {
        let (a, b) = two(csts, pos)?;
        Ok(ExternDecl {
            ident: ident(a)?,
            typ: self.parse_type(b)?,
            pos: pos.clone(),
        })
    }

    fn parse_externs(
        &mut self,
        decls_csts: &[(Vec<CST<'s>>, SrcPos<'s>)],
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

    fn parse_constraint(&mut self, cst: &CST<'s>) -> PRes<'s, &'s str> {
        match *cst {
            CST::Ident("Num", _) => Ok("Num"),
            CST::Ident(s, ref pos) => Err(UndefConstr(pos.clone(), s)),
            _ => Err(InvalidConstr(cst.pos().clone())),
        }
    }

    /// Parse a definition of constraints
    fn parse_constraints_def(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        let (first, rest) = split_first(csts, pos)?;
        let id = ident(first)?;
        let (name, pos) = (id.s, id.pos);
        if name.starts_with(char::is_lowercase) {
            if tvars.contains_key(name) {
                let first_pos = tvars.get(name).unwrap().1.clone();
                Err(TVarDuplDef {
                    name: name,
                    pos: pos.clone(),
                    prev_pos: first_pos,
                })
            } else {
                let tv = TVar {
                    id: self.type_var_gen.gen(),
                    constrs: rest.iter()
                        .map(|cst| self.parse_constraint(cst))
                        .collect::<PRes<'s, BTreeSet<&'s str>>>()?,
                    explicit: Some(name),
                };
                tvars.insert(name, (tv.clone(), pos.clone()));
                Ok(Type::Var(tv))
            }
        } else {
            Err(InvalidTVar(pos.clone()))
        }
    }

    fn parse_func_type(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        let (ret, init) = split_last(csts, pos)?;
        let (last_param, init_params) = split_last(init, pos)?;

        let last_fn = Type::new_func(
            self.parse_type_with_tvars(tvars, last_param)?,
            self.parse_type_with_tvars(tvars, ret)?,
        );
        init_params.iter().rev().fold(Ok(last_fn), |acc, t| {
            Ok(Type::new_func(self.parse_type_with_tvars(tvars, t)?, acc?))
        })
    }

    fn parse_cons_type(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        let (a, b) = two(csts, pos)?;
        let car = self.parse_type_with_tvars(tvars, a)?;
        let cdr = self.parse_type_with_tvars(tvars, b)?;
        Ok(Type::new_cons(car, cdr))
    }

    fn parse_ptr_type(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        self.parse_type_with_tvars(tvars, one(csts, pos)?)
            .map(Type::new_ptr)
    }

    fn parse_type_sexpr(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        app: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        let (first, rest) = split_first(app, pos)?;
        let id = ident(first)?;
        let (s, p) = (id.s, id.pos);
        match s {
            ":" => self.parse_constraints_def(tvars, rest, pos),
            "->" => self.parse_func_type(tvars, rest, pos),
            "Cons" => self.parse_cons_type(tvars, rest, pos),
            "Ptr" => self.parse_ptr_type(tvars, rest, pos),
            _ => Err(UndefTypeCon(p.clone(), s)),
        }
    }

    fn parse_type_ident(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        id: &'s str,
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Type<'s>> {
        match id {
            "_" => Ok(self.gen_type_var()),
            "Nil" => Ok(TYPE_NIL.clone()),
            // The type identifier starts with a lowercase letter => Is a type variable
            s if s.starts_with(char::is_lowercase) => {
                let local = TVar {
                    id: self.type_var_gen.gen(),
                    constrs: BTreeSet::new(),
                    explicit: Some(s),
                };
                let tv = tvars.entry(s).or_insert((local, pos.clone())).0.clone();
                Ok(Type::Var(tv))
            }
            // Doesn't start with lowercase => Is a type constant e.g. Int32
            s => Ok(Type::Const(s, Some(pos.clone()))),
        }
    }

    /// Parse a syntax tree as a `Type`, keeping track och implicitly defined type variables
    fn parse_type_with_tvars(
        &mut self,
        tvars: &mut BTreeMap<&'s str, (TVar<'s>, SrcPos<'s>)>,
        tree: &CST<'s>,
    ) -> PRes<'s, Type<'s>> {
        match *tree {
            CST::SExpr(ref sexp, ref pos) => self.parse_type_sexpr(tvars, sexp, pos),
            CST::Ident(s, ref pos) => self.parse_type_ident(tvars, s, &pos),
            _ => Err(InvalidType(tree.pos().clone())),
        }
    }

    /// Parse a syntax tree as a `Type`
    fn parse_type(&mut self, tree: &CST<'s>) -> PRes<'s, Type<'s>> {
        self.parse_type_with_tvars(&mut BTreeMap::new(), tree)
            .map(|t| t.canonicalize())
    }

    fn parse_app_pattern(&mut self, app: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Pattern<'s>> {
        let (fst, rest) = split_first(app, pos)?;
        let f_id = ident(fst)?;
        let first_param = first(rest, pos)?;
        let last_param = last(rest, pos)?;
        let params_pos = first_param.pos().to(last_param.pos());
        let params_ids = rest.iter().map(|a| ident(a)).collect::<PRes<Vec<_>>>()?;
        Ok(Pattern::Func(f_id, (params_ids, params_pos)))
    }

    /// Parse a syntax tree as a Pattern
    fn parse_pattern(&mut self, cst: &CST<'s>) -> PRes<'s, Pattern<'s>> {
        match *cst {
            CST::Ident(s, ref pos) => Ok(Pattern::Var(Ident {
                s,
                pos: pos.clone(),
            })),
            CST::SExpr(ref app, ref pos) => self.parse_app_pattern(app, pos),
            _ => Err(InvalidPatt(cst.pos().clone())),
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

    /// Parse a first `CST` and some following `CST`s as a procedure and some arguments,
    /// i.e. a function application
    fn parse_app(
        &mut self,
        func_cst: &CST<'s>,
        args_csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, App<'s>> {
        let func = self.parse_expr(func_cst)?;
        let args = args_csts
            .iter()
            .map(|a| self.parse_expr(a))
            .collect::<PRes<Vec<_>>>()?;
        self.new_multary_app(func, &args, &pos)
    }

    /// Parse a list of `CST`s as parts of an `If` conditional
    fn parse_if(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, If<'s>> {
        let (p, c, a) = three(csts, pos)?;
        Ok(If {
            predicate: self.parse_expr(p)?,
            consequent: self.parse_expr(c)?,
            alternative: self.parse_expr(a)?,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    /// Parse the `else` clause of a `cond`
    fn parse_else_clause(&mut self, cst: &CST<'s>) -> PRes<'s, Expr<'s>> {
        let (pred, conseq) = pair(cst)?;
        constant(ident_s(pred)?, "else", Expected(pred.pos().clone(), "else"))
            .and_then(|_| self.parse_expr(conseq))
    }

    /// Parse a clause of a `cond`
    fn parse_cond_clause(&mut self, cst: &CST<'s>) -> PRes<'s, (Expr<'s>, Expr<'s>)> {
        let (p, c) = pair(cst)?;
        Ok((self.parse_expr(p)?, self.parse_expr(c)?))
    }

    /// Parse a sequence of token trees as the clauses of a `cond` special form
    ///
    /// Translate to nested `If`s
    fn parse_cond(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Expr<'s>> {
        let (last, init) = split_last(csts, pos)?;
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
            param_type: last.1.clone(),
            body: body,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        };
        Ok(init.iter()
            .rev()
            .cloned()
            .fold(innermost, |inner, param| Lambda {
                param_ident: param.0,
                param_type: param.1,
                body: Expr::Lambda(Box::new(inner)),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            }))
    }

    /// Parse a list of `CST`s as the parts of a `Lambda`
    fn parse_lambda(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Lambda<'s>> {
        let (a, b) = two(csts, pos)?;
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
        patt: &CST<'s>,
        maybe_typ: Option<&CST<'s>>,
        val: &CST<'s>,
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Binding<'s>> {
        let typ = maybe_typ
            .map(|c| self.parse_type(c))
            .unwrap_or_else(|| Ok(self.gen_type_var()))?;
        Ok(match self.parse_pattern(patt)? {
            Pattern::Var(ident) => Binding {
                ident: ident,
                typ: typ,
                val: self.parse_expr(val)?,
                mono_insts: BTreeMap::new(),
                pos: pos.clone(),
            },
            Pattern::Func(f_id, (params_ids, params_pos)) => {
                let params = params_ids
                    .into_iter()
                    .map(|id| (id, self.gen_type_var()))
                    .collect::<Vec<_>>();
                let body = self.parse_expr(val)?;
                Binding {
                    ident: f_id,
                    typ: typ,
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
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Binding<'s>> {
        let (patt, val) = two(csts, pos)?;
        self.parse_binding(patt, None, val, pos)
    }

    fn parse_typed_binding(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Binding<'s>> {
        let (patt, typ, val) = three(csts, pos)?;
        self.parse_binding(patt, Some(typ), val, pos)
    }

    fn parse_bindings_to_flat_map(
        &mut self,
        defs: &[(bool, &[CST<'s>], SrcPos<'s>)],
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
        defs: &[(bool, &[CST<'s>], SrcPos<'s>)],
    ) -> PRes<'s, TopologicallyOrderedDependencyGroups<'s>> {
        self.parse_bindings_to_flat_map(defs)
            .map(flat_bindings_to_topologically_ordered)
    }

    fn parse_let_bindings(
        &mut self,
        csts: &[CST<'s>],
    ) -> PRes<'s, TopologicallyOrderedDependencyGroups<'s>> {
        let mut bindings_csts = Vec::new();
        for cst in csts {
            let binding_pair = sexpr(cst)?;
            bindings_csts.push((false, binding_pair.clone(), cst.pos().clone()))
        }
        self.parse_bindings(&bindings_csts)
    }

    /// Parse a `let` special form and return as an invocation of a lambda
    fn parse_let(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Let<'s>> {
        let (a, b) = two(csts, &pos)?;
        let binds_csts = sexpr(a)?;
        Ok(Let {
            bindings: self.parse_let_bindings(binds_csts)?,
            body: self.parse_expr(b)?,
            typ: self.gen_type_var(),
            pos: pos.clone(),
        })
    }

    /// Parse a list of `CST`s as a `TypeAscript`
    fn parse_type_ascript(
        &mut self,
        csts: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, TypeAscript<'s>> {
        let (a, b) = two(csts, pos)?;
        Ok(TypeAscript {
            typ: self.parse_type(b)?,
            expr: self.parse_expr(a)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `CST`s as a `Cons` pair
    fn parse_cons(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Cons<'s>> {
        let (a, b) = two(csts, pos)?;
        Ok(Cons {
            typ: self.gen_type_var(),
            car: self.parse_expr(a)?,
            cdr: self.parse_expr(b)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `CST`s as a `car` operation
    fn parse_car(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Car<'s>> {
        Ok(Car {
            typ: self.gen_type_var(),
            expr: self.parse_expr(one(csts, pos)?)?,
            pos: pos.clone(),
        })
    }

    /// Parse a list of `CST`s as a `cdr` operation
    fn parse_cdr(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Cdr<'s>> {
        Ok(Cdr {
            typ: self.gen_type_var(),
            expr: self.parse_expr(one(csts, pos)?)?,
            pos: pos.clone(),
        })
    }

    /// Parse a type cast
    ///
    /// `(cast VAL TYPE)`, e.g. `(cast (: 1 Int32) Int64)`
    fn parse_cast(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, Cast<'s>> {
        let (a, b) = two(csts, pos)?;
        Ok(Cast {
            expr: self.parse_expr(a)?,
            typ: self.parse_type(b)?,
            pos: pos.clone(),
        })
    }

    /// Parse a `CST` as an `Expr`
    fn parse_expr(&mut self, cst: &CST<'s>) -> PRes<'s, Expr<'s>> {
        match *cst {
            CST::SExpr(ref sexpr, ref pos) => {
                if let Some((head, tail)) = sexpr.split_first() {
                    match *head {
                        CST::Ident("if", _) => Ok(Expr::If(Box::new(self.parse_if(tail, &pos)?))),
                        CST::Ident("lambda", _) => {
                            Ok(Expr::Lambda(Box::new(self.parse_lambda(tail, pos)?)))
                        }
                        CST::Ident("let", _) => Ok(Expr::Let(Box::new(self.parse_let(tail, pos)?))),
                        CST::Ident(":", _) => Ok(Expr::TypeAscript(Box::new(
                            self.parse_type_ascript(tail, pos)?,
                        ))),
                        CST::Ident("cons", _) => {
                            Ok(Expr::Cons(Box::new(self.parse_cons(tail, pos)?)))
                        }
                        CST::Ident("car", _) => Ok(Expr::Car(Box::new(self.parse_car(tail, pos)?))),
                        CST::Ident("cdr", _) => Ok(Expr::Cdr(Box::new(self.parse_cdr(tail, pos)?))),
                        CST::Ident("cast", _) => {
                            Ok(Expr::Cast(Box::new(self.parse_cast(tail, pos)?)))
                        }

                        // "Macros"
                        CST::Ident("cond", _) => self.parse_cond(tail, pos),
                        _ => Ok(Expr::App(Box::new(self.parse_app(&sexpr[0], tail, pos)?))),
                    }
                } else {
                    Ok(Expr::Nil(Nil { pos: pos.clone() }))
                }
            }
            CST::Ident("nil", ref pos) => Ok(Expr::Nil(Nil { pos: pos.clone() })),
            CST::Ident("true", ref pos) => Ok(Expr::Bool(Bool {
                val: true,
                pos: pos.clone(),
            })),
            CST::Ident("false", ref pos) => Ok(Expr::Bool(Bool {
                val: false,
                pos: pos.clone(),
            })),
            CST::Ident(ident, ref pos) => Ok(Expr::Variable(Variable {
                ident: Ident::new(ident, pos.clone()),
                typ: self.gen_type_var(),
            })),
            CST::Num(num, ref pos) => Ok(Expr::NumLit(NumLit {
                lit: num,
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
            CST::Str(ref s, ref pos) => Ok(Expr::StrLit(StrLit {
                lit: s.clone(),
                typ: self.gen_type_var(),
                pos: pos.clone(),
            })),
        }
    }

    /// Parse the members of an algebraic data type variant
    fn parse_data_type_variant_members(
        &mut self,
        cs: &[CST<'s>],
        pos: &SrcPos<'s>,
    ) -> PRes<'s, Vec<Type<'s>>> {
        first(cs, pos)?;
        cs.iter().map(|c| self.parse_type(c)).collect()
    }

    /// Parse a variant of a data type definition
    fn parse_data_type_variant(&mut self, c: &CST<'s>) -> PRes<'s, AdtVariant<'s>> {
        match *c {
            CST::Ident(s, ref p) => Ok(AdtVariant {
                name: Ident {
                    s: s,
                    pos: p.clone(),
                },
                members: vec![],
                pos: p.clone(),
            }),
            CST::SExpr(ref cs, ref p) => {
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
    fn parse_data_type_variants(&mut self, cs: &[CST<'s>]) -> PRes<'s, Vec<AdtVariant<'s>>> {
        cs.iter().map(|c| self.parse_data_type_variant(c)).collect()
    }

    /// Parse a data type definition
    fn parse_data_type_def(&mut self, csts: &[CST<'s>], pos: &SrcPos<'s>) -> PRes<'s, AdtDef<'s>> {
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

    fn parse_data_type_defs(
        &mut self,
        defs_csts: &[(Vec<CST<'s>>, SrcPos<'s>)],
    ) -> PRes<'s, BTreeMap<&'s str, AdtDef<'s>>> {
        let mut datas = BTreeMap::new();
        for &(ref def_csts, ref pos) in defs_csts {
            let def = self.parse_data_type_def(def_csts, pos)?;
            let def_pos = def.pos.clone();
            if let Some(prev_def) = datas.insert(def.name.s, def) {
                return Err(DataTypeDuplDef {
                    pos: def_pos,
                    name: prev_def.name.s,
                    prev_pos: prev_def.pos.clone(),
                });
            }
        }
        Ok(datas)
    }

    fn _get_top_level_csts<'c>(
        &mut self,
        csts: &'c [CST<'s>],
        externs: &mut Vec<(Vec<CST<'s>>, SrcPos<'s>)>,
        globals: &mut Vec<(bool, Vec<CST<'s>>, SrcPos<'s>)>,
        datas: &mut Vec<(Vec<CST<'s>>, SrcPos<'s>)>,
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
                "data" => datas.push((rest.to_vec(), pos.clone())),
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
                self._get_top_level_csts(&import_csts, externs, globals, datas)?
            }
        }
        Ok(())
    }

    /// Separate `csts` into token trees for externs, and globals
    ///
    /// Recursively follow imports and get top level csts from there as well
    fn get_top_level_csts<'c>(
        &mut self,
        csts: &'c [CST<'s>],
    ) -> PRes<
        's,
        (
            Vec<(Vec<CST<'s>>, SrcPos<'s>)>,
            Vec<(bool, Vec<CST<'s>>, SrcPos<'s>)>,
            Vec<(Vec<CST<'s>>, SrcPos<'s>)>,
        ),
    > {
        let (mut externs, mut globals, mut datas) = (Vec::new(), Vec::new(), Vec::new());
        self._get_top_level_csts(csts, &mut externs, &mut globals, &mut datas)?;
        Ok((externs, globals, datas))
    }

    fn parse_ast(&mut self, csts: &[CST<'s>]) -> PRes<'s, Ast<'s>> {
        let (externs_csts, globals_csts, datas_csts) = self.get_top_level_csts(csts)?;
        let globals_csts_slc = globals_csts
            .iter()
            .map(|&(is_typed, ref v, ref p)| (is_typed, v.as_slice(), p.clone()))
            .collect::<Vec<_>>();
        Ok(Ast {
            externs: self.parse_externs(&externs_csts)?,
            globals: self.parse_bindings(&globals_csts_slc)?,
            datas: self.parse_data_type_defs(&datas_csts)?,
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
    use lib::front::lex::CST;
    use lib::front::*;
    use lib::front::ast::*;
    use super::Parser;

    fn dummy_cident(s: &str) -> CST {
        CST::Ident(s, SrcPos::new_dummy())
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
