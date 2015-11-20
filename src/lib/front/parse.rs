// The MIT License (MIT)
//
// Copyright (c) 2015 Johan Johansson
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::collections::HashMap;
use std::fmt::{ self, Display };
use std::borrow::Cow;
use super::SrcPos;
use super::lex::{ TokenTree, TokenTreeMeta };
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
			ArityMis(expected, found) =>
				write!(f, "Arity mismatch. Expected {}, found {}", expected, found),
			Expected(e) => write!(f, "Expected {}", e),
		}
	}
}

struct Parser;

impl<'src> Parser {
	pub fn parse_type(ttm: &TokenTreeMeta<'src>) -> Type<'src> {
		match ttm.tt {
			TokenTree::List(ref construct) if ! construct.is_empty() => match construct[0].tt {
				TokenTree::Ident(constructor) => Type::Construct(
					constructor,
					construct[1..].iter().map(Self::parse_type).collect()),
				_ => construct[0].pos.error(Invalid("type constructor")),
			},
			TokenTree::List(_) => TYPE_NIL.clone(),
			TokenTree::Ident("_") => Type::Unknown,
			TokenTree::Ident(basic) => Type::Basic(basic),
			TokenTree::Num(_) => ttm.pos.error(Mismatch("type", "numeric literal")),
			TokenTree::Str(_) => ttm.pos.error(Mismatch("type", "string literal")),
		}
	}

	fn parse_binding(ttm: &TokenTreeMeta<'src>) -> Ident<'src> {
		match ttm.tt {
			TokenTree::Ident(ident) => Ident::new(ident, ttm.pos.clone()),
			_ => ttm.pos.error(Invalid("binding"))
		}
	}

	/// Parse a path
	fn parse_path(ttm: &TokenTreeMeta<'src>) -> Path<'src> {
		match ttm.tt {
			TokenTree::Ident(s) => Path::from_str(s, ttm.pos.clone()),
			_ => ttm.pos.error(Expected("path")),
		}
	}

	/// # Rust equivalent
	///
	/// `path\to\item` => `path::to::item`
	/// `(path\to\module sub\item1 item2)` == `path::to::module{ sub::item1, item2 }``
	/// `(lvl1::lvl2 (lvl2a lvl3a lvl3b) lvl2b)` == `use lvl1::lvl2::{ lvl2a::{ lvl3a, lvl3b}, lvl2b }`
	fn parse_compound_path(ttm: &TokenTreeMeta<'src>) -> Vec<Path<'src>> {
		match ttm.tt {
			TokenTree::List(ref compound) => if let Some((chead, tail)) = compound.split_first() {
				let path_head = Self::parse_path(chead);
				tail.iter()
					.map(Self::parse_compound_path)
					.flat_map(|v| v)
					.map(|sub| path_head.clone()
							.concat(&sub)
							.unwrap_or_else(|_| sub.pos.error("Sub-path is absolute")))
					.collect()
			} else {
				ttm.pos.error("Empty path compound")
			},
			TokenTree::Ident(ident) => vec![Path::from_str(ident, ttm.pos.clone())],
			TokenTree::Num(_) | TokenTree::Str(_) => ttm.pos.error(Expected("path")),
		}
	}

	fn parse_use(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Use<'src> {
		Use{
			paths: tts.iter().map(Self::parse_compound_path).flat_map(|paths| paths).collect(),
			pos: pos,
		}
	}

	fn parse_const_def(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>)
		-> (Ident<'src>, ConstDef<'src>)
	{
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		} else {
			match tts[0].tt {
				TokenTree::Ident(name) => (
					Ident::new(name, tts[0].pos.clone()),
					ConstDef { body: Self::parse_expr(&tts[1]), pos: pos }),
				_ => tts[0].pos.error(Expected("identifier")),
			}
		}
	}

	fn parse_sexpr(
		proc_ttm: &TokenTreeMeta<'src>,
		args_tts: &[TokenTreeMeta<'src>],
		pos: SrcPos<'src>
	) -> Call<'src> {
		Call{
			proced: Self::parse_expr(proc_ttm),
			args: args_tts.iter().map(Self::parse_expr).collect(),
			pos: pos
		}
	}

	/// Parse a `Block` from tokens. Returns `None` if there are no expressions in the block.
	fn parse_block(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Option<Block<'src>> {
		let (uses, const_defs, extern_funcs, exprs) = Parser::parse_items(tts);
		if exprs.is_empty() {
			None
		} else {
			Some(Block{
				uses: uses,
				const_defs: const_defs,
				extern_funcs: extern_funcs,
				exprs: exprs,
				pos: pos
			})
		}
	}

	fn parse_if(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> If<'src> {
		if tts.len() != 3 {
			pos.error(ArityMis(3, tts.len()))
		}
		If {
			predicate: Self::parse_expr(&tts[0]),
			consequent: Self::parse_expr(&tts[1]),
			alternative: Self::parse_expr(&tts[2]),
			pos: pos
		}
	}

	fn parse_lambda(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Lambda<'src> {
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		}
		match tts[0].tt {
			TokenTree::List(ref param_tts) => Lambda {
				params: param_tts.iter()
					.map(|param_tt| Param::new(Self::parse_binding(param_tt), Type::Unknown))
					.collect(),
				body: Self::parse_expr(&tts[1]),
				pos: pos
			},
			_ => tts[0].pos.error(Expected("list")),
		}
	}

	fn parse_var_def(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> VarDef<'src> {
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		}
		match tts[0].tt {
			TokenTree::Ident(binding) => VarDef {
				binding: Ident::new(binding, tts[0].pos.clone()),
				mutable: false,
				body: Self::parse_expr(&tts[1]),
				typ: Type::Unknown,
				pos: pos
			},
			_ => tts[0].pos.error(Expected("list")),
		}
	}

	fn parse_assign(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Assign<'src> {
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		}
		Assign {
			lhs: Self::parse_expr(&tts[0]),
			rhs: Self::parse_expr(&tts[1]),
			typ: Type::Unknown,
			pos: pos,
		}
	}

	fn parse_deref(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Deref<'src> {
		if tts.len() != 1 {
			pos.error(ArityMis(1, tts.len()))
		}
		Deref {
			r: Self::parse_expr(&tts[0]),
			pos: pos,
		}
	}

	fn parse_type_ascript(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> TypeAscript<'src> {
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		}
		TypeAscript {
			typ: Self::parse_type(&tts[0]),
			expr: Self::parse_expr(&tts[1]),
			pos: pos,
		}
	}

	fn parse_quoted_expr(ttm: &TokenTreeMeta<'src>) -> Expr<'src> {
		match ttm.tt {
			TokenTree::List(ref list) => Expr::Call(Box::new(Call{
				proced: Expr::Binding(Binding {
					path: Path::from_str("list", ttm.pos.clone()),
					typ: Type::Unknown
				}),
				args: list.iter()
					.map(|li| Self::parse_quoted_expr(li))
					.collect(),
				pos: ttm.pos.clone(),
			})),
			TokenTree::Ident(ident) => Expr::Symbol(Symbol {
				ident: Ident::new(ident, ttm.pos.clone()),
				typ: Type::Unknown
			}),
			TokenTree::Num(num) => Expr::NumLit(NumLit {
				lit: num,
				typ: Type::Unknown,
				pos: ttm.pos.clone()
			}),
			TokenTree::Str(ref s) => Expr::StrLit(StrLit {
				lit: s.clone(),
				typ: Type::Unknown,
				pos: ttm.pos.clone()
			}),
		}
	}

	pub fn parse_expr(ttm: &TokenTreeMeta<'src>) -> Expr<'src> {
		match ttm.tt {
			TokenTree::List(ref sexpr) => if let Some((head, tail)) = sexpr.split_first() {
				match head.tt {
					TokenTree::Ident("quote") => if let Some(to_quote) = tail.first() {
						Self::parse_quoted_expr(to_quote)
					} else {
						ttm.pos.error(ArityMis(1, sexpr.len()))
					},
					TokenTree::Ident("if") =>
						Expr::If(Box::new(Self::parse_if(tail, ttm.pos.clone()))),
					TokenTree::Ident("lambda") =>
						Expr::Lambda(Box::new(Self::parse_lambda(tail, ttm.pos.clone()))),
					TokenTree::Ident("block") => Self::parse_block(tail, ttm.pos.clone())
						.map(|block| Expr::Block(Box::new(block)))
						.unwrap_or(Expr::Nil(Nil { typ: Type::Unknown, pos: ttm.pos.clone() })),
					TokenTree::Ident("def-var") =>
						Expr::VarDef(Box::new(Self::parse_var_def(tail, ttm.pos.clone()))),
					TokenTree::Ident("def-var-mut") => Expr::VarDef(Box::new(VarDef {
						mutable: true,
						.. Self::parse_var_def(tail, ttm.pos.clone())
					})),
					TokenTree::Ident("set") =>
						Expr::Assign(Box::new(Self::parse_assign(tail, ttm.pos.clone()))),
					TokenTree::Ident("deref") if tail.len() == 1 =>
						Expr::Deref(Box::new(Self::parse_deref(tail, ttm.pos.clone()))),
					TokenTree::Ident(":") => Expr::TypeAscript(Box::new(
						Self::parse_type_ascript(tail, ttm.pos.clone()))),
					_ => Expr::Call(Box::new(Self::parse_sexpr(&sexpr[0], tail, ttm.pos.clone()))),
				}
			} else {
				Expr::Nil(Nil { typ: Type::Unknown, pos: ttm.pos.clone() })
			},
			TokenTree::Ident("true") => Expr::Bool(Bool {
				val: true,
				typ: Type::Unknown,
				pos: ttm.pos.clone()
			}),
			TokenTree::Ident("false") => Expr::Bool(Bool {
				val: false,
				typ: Type::Unknown,
				pos: ttm.pos.clone()
			}),
			TokenTree::Ident(ident) => Expr::Binding(Binding {
				path: Path::from_str(ident, ttm.pos.clone()),
				typ: Type::Unknown,
			}),
			TokenTree::Num(num) =>
				Expr::NumLit(NumLit { lit: num, typ: Type::Unknown, pos: ttm.pos.clone() }),
			TokenTree::Str(ref s) => Expr::StrLit(StrLit {
				lit: s.clone(),
				typ: Type::Unknown,
				pos: ttm.pos.clone()
			}),
		}
	}

	fn parse_extern_const(tts: &[TokenTreeMeta<'src>], pos: &SrcPos<'src>)
		-> (Ident<'src>, Type<'src>)
	{
		if tts.len() != 2 {
			pos.error("Invalid external constant declaration. Expected identifier and type")
		} else {
			match tts[0].tt {
				TokenTree::Ident(name) => {
					let typ = Self::parse_type(&tts[1]);
					if ! typ.is_fully_known() {
						tts[1].pos.error("Type of external constant must be fully specified")
					}
					(Ident::new(name, tts[0].pos.clone()), typ)
				},
				_ => tts[0].pos.error(Expected("identifier")),
			}
		}
	}

	/// Parse TokenTree:s as a list of items
	fn parse_items(tts: &[TokenTreeMeta<'src>]) -> (
		Vec<Use<'src>>,
		HashMap<Ident<'src>, ConstDef<'src>>,
		HashMap<Ident<'src>, Type<'src>>,
		Vec<Expr<'src>>
	) {
		let mut uses = Vec::new();
		let (mut const_defs, mut extern_funcs) = (HashMap::new(), HashMap::new());
		let mut exprs = Vec::new();

		for ttm in tts {
			match ttm.tt {
				TokenTree::List(ref sexpr) if ! sexpr.is_empty() => match sexpr[0].tt {
					TokenTree::Ident("use") => uses.push(
						Self::parse_use(&sexpr[1..], ttm.pos.clone())),
					TokenTree::Ident("def-const") => {
						let (id, def) = Self::parse_const_def(&sexpr[1..], ttm.pos.clone());
						let id_s = id.s;

						if const_defs.insert(id, def).is_some() {
							ttm.pos.error(format!("Duplicate constant definition `{}`", id_s))
						}
					},
					TokenTree::Ident("extern-proc") => {
						let (id, typ) = Self::parse_extern_const(&sexpr[1..], &ttm.pos);
						let id_s = id.s;

						if extern_funcs.insert(id, typ).is_some() {
							ttm.pos.error(
								format!("Duplicate external constant declaration `{}`", id_s))
						}
					},
					_ => exprs.push(Self::parse_expr(ttm)),
				},
				_ => exprs.push(Self::parse_expr(ttm)),
			}
		}

		(uses, const_defs, extern_funcs, exprs)
	}

	fn parse_ast(tts: &[TokenTreeMeta<'src>]) -> AST<'src> {
		let (uses, const_defs, extern_funcs, exprs) = Self::parse_items(tts);

		for expr in exprs {
			expr.pos().error("Expression at top level");
		}
		AST{ uses: uses, const_defs: const_defs, extern_funcs: extern_funcs }
	}
}

pub fn parse<'src>(tts: &[TokenTreeMeta<'src>]) -> AST<'src> {
	Parser::parse_ast(tts)
}
