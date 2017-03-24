// TODO: Verify that all types are known

use lib::ScopeStack;
use lib::error;
use lib::front::ast::*;
use std::collections::HashMap;
use std::mem::replace;

#[derive(Debug)]
enum Usage {
    Used,
    Unused,
}
impl Usage {
    fn is_used(&self) -> bool {
        match *self {
            Usage::Used => true,
            _ => false,
        }
    }
    fn is_unused(&self) -> bool {
        !self.is_used()
    }
}

struct Cleaner<'src> {
    static_defs: ScopeStack<Ident<'src>, Option<(StaticDef<'src>, Usage)>>,
}
impl<'src> Cleaner<'src> {
    fn new() -> Cleaner<'src> {
        Cleaner { static_defs: ScopeStack::new() }
    }

    fn clean_path(&mut self, path: &Path<'src>) {
        if let Some((id, height)) =
            path.as_ident()
                .and_then(|id| {
                    self.static_defs
                        .get_height(id)
                        .map(|height| (id, height))
                }) {
            let maybe_def = replace(self.static_defs.get_at_height_mut(id, height).unwrap(),
                                    None);

            if let Some((mut def, mut usage)) = maybe_def {
                if usage.is_unused() {
                    usage = Usage::Used;

                    self.clean_static_def(&mut def);
                }

                self.static_defs.update(id, Some((def, usage)));
            }
        }
    }

    fn clean_call(&mut self, call: &mut Call<'src>) {
        self.clean_expr(&mut call.proced);

        for arg in &mut call.args {
            self.clean_expr(arg);
        }
    }

    fn clean_block(&mut self, block: &mut Block<'src>) {
        self.static_defs.push(replace(&mut block.static_defs, HashMap::new())
            .into_iter()
            .map(|(k, def)| (k, Some((def, Usage::Unused))))
            .collect());

        for expr in &mut block.exprs {
            self.clean_expr(expr);
        }

        block.static_defs = self.static_defs
                                .pop()
                                .expect("ICE: clean_block: ScopeStack was empty when replacing \
                                         Block const defs")
                                .into_iter()
                                .filter_map(|(key, maybe_def)| {
            match maybe_def.expect("ICE: clean_block: None when unmapping block const def") {
                (def, Usage::Used) => Some((key, def)),
                (_, Usage::Unused) => {
                    key.pos.warn(format!("Unused constant `{}`", key));
                    None
                }
            }
        })
                                .collect();
    }

    fn clean_if(&mut self, cond: &mut If<'src>) {
        for expr in &mut [&mut cond.predicate, &mut cond.consequent, &mut cond.alternative] {
            self.clean_expr(expr);
        }
    }

    fn clean_lambda(&mut self, lambda: &mut Lambda<'src>) {
        self.clean_expr(&mut lambda.body);
    }

    fn clean_var_def(&mut self, def: &mut VarDef<'src>) {
        self.clean_expr(&mut def.body);
    }

    fn clean_assign(&mut self, assign: &mut Assign<'src>) {
        self.clean_expr(&mut assign.lhs);
        self.clean_expr(&mut assign.rhs);
    }

    fn clean_expr(&mut self, expr: &mut Expr<'src>) {
        match *expr {
            Expr::Binding(ref bnd) => self.clean_path(&bnd.path),
            Expr::Call(ref mut call) => self.clean_call(call),
            Expr::Block(ref mut block) => self.clean_block(block),
            Expr::If(ref mut cond) => self.clean_if(cond),
            Expr::Lambda(ref mut lambda) => self.clean_lambda(lambda),
            Expr::VarDef(ref mut def) => self.clean_var_def(def),
            Expr::Assign(ref mut assign) => self.clean_assign(assign),
            Expr::TypeAscript(ref mut ascr) => self.clean_expr(&mut ascr.expr),
            Expr::Deref(ref mut deref) => self.clean_expr(&mut deref.r),
            Expr::Transmute(ref mut trans) => self.clean_expr(&mut trans.arg),
            Expr::Bool(_) | Expr::Nil(_) | Expr::NumLit(_) | Expr::StrLit(_) | Expr::Symbol(_) => {
                ()
            }
        }
    }

    fn clean_static_def(&mut self, def: &mut StaticDef<'src>) {
        self.clean_expr(&mut def.body)
    }
}

pub fn clean_ast(ast: &mut Module) {
    let mut cleaner = Cleaner::new();

    cleaner.static_defs.push(replace(&mut ast.static_defs, HashMap::new())
        .into_iter()
        .map(|(k, def)| (k, Some((def, Usage::Unused))))
        .collect());

    let main = replace(cleaner.static_defs
                              .get_mut("main")
                              .unwrap_or_else(|| error("No `main` procedure found")),
                       None);

    let (mut main_def, _) = main.unwrap();

    cleaner.clean_static_def(&mut main_def);

    cleaner.static_defs.update("main", Some((main_def, Usage::Used)));

    ast.static_defs = cleaner.static_defs
                             .pop()
                             .expect("ICE: clean_ast: ScopeStack was empty when replacing AST \
                                      const defs")
                             .into_iter()
                             .filter_map(|(key, maybe_def)| {
        match maybe_def.expect(&format!("ICE: clean_ast: `{}` was None when unmapping AST \
                                         const def",
                                        key)) {
            (def, Usage::Used) => Some((key, def)),
            (_, Usage::Unused) => {
                key.pos.warn(format!("Unused constant `{}`", key));
                None
            }
        }
    })
                             .collect();
}
