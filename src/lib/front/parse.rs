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
use super::SrcPos;
use super::lex::{ StrLit, TokenTree, TokenTreeMeta };
use self::ParseErr::*;

pub enum ParseErr {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<'src> {
	Unknown,
	Basic(&'src str),
	Construct(&'src str, Vec<Type<'src>>),
}
/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'src> Type<'src> {
	pub fn new_proc(mut arg_tys: Vec<Type<'src>>, return_ty: Type<'src>) -> Self {
		arg_tys.push(return_ty);
		Type::Construct("proc", arg_tys)
	}
	pub fn nil() -> Self { Type::Basic("Nil") }

	pub fn parse(ttm: &TokenTreeMeta<'src>) -> Type<'src> {
		match ttm.tt {
			TokenTree::List(ref construct) if ! construct.is_empty() => match construct[0].tt {
				TokenTree::Ident(constructor) => Type::Construct(
					constructor,
					construct[1..].iter().map(Type::parse).collect()),
				_ => construct[0].pos.error(Invalid("type constructor")),
			},
			TokenTree::List(_) => Type::nil(),
			TokenTree::Ident("_") => Type::Unknown,
			TokenTree::Ident(basic) => Type::Basic(basic),
			TokenTree::Num(_) => ttm.pos.error(Mismatch("type", "numeric literal")),
			TokenTree::Str(_) => ttm.pos.error(Mismatch("type", "string literal")),
		}
	}
}
impl<'src> fmt::Display for Type<'src> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Type::Unknown => write!(f, "_"),
			Type::Basic(basic) => write!(f, "{}", basic),
			Type::Construct(constructor, ref args) => write!(f, "({} {})",
				constructor,
				args.iter().fold(String::new(), |acc, arg| format!("{} {}", acc, arg))),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedBinding<'src> {
	pub ident: &'src str,
	pub typ: Type<'src>,
	pub pos: SrcPos<'src>,
}
impl<'src> TypedBinding<'src> {
	fn parse(ttm: &TokenTreeMeta<'src>) -> Self {
		match ttm.tt {
			TokenTree::List(ref tb) if ! tb.is_empty() && tb[0].tt == TokenTree::Ident(":") =>
				if tb.len() == 3 {
					match tb[2].tt {
						TokenTree::Ident(ident) => TypedBinding{
							ident: ident,
							typ: Type::parse(&tb[1]),
							pos: ttm.pos.clone()
						},
						_ => tb[2].pos.error(Invalid("binding")),
					}
				} else {
					ttm.pos.error(Invalid("type ascription"))
				},
			TokenTree::Ident(ident) =>
				TypedBinding{ ident: ident, typ: Type::Unknown, pos: ttm.pos.clone() },
			_ => ttm.pos.error(Invalid("binding"))
		}
	}
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Path<'src> {
	parts: Vec<&'src str>,
	is_absolute: bool,
	pub pos: SrcPos<'src>
}
impl<'src> Path<'src> {
	pub fn is_absolute(&self) -> bool { self.is_absolute }

	/// If self is just a simple ident, return it as Some
	pub fn ident(&self) -> Option<&str> {
		if ! self.is_absolute { self.parts.first().map(|&s| s) } else { None }
	}

	/// Concatenates two paths.
	///
	/// Returns both `self` as `Err` if right hand path is absolute
	pub fn concat(mut self, other: &Self) -> Result<Self, Self> {
		if other.is_absolute {
			Err(self)
		} else {
			self.parts.extend(other.parts.iter());
			Ok(self)
		}
	}

	pub fn to_string(&self) -> String {
		format!("{}{}{}",
			if self.is_absolute() { "\\" } else { "" },
			self.parts[0],
			self.parts[1..].iter().fold(String::new(), |acc, p| acc + "\\" + p))
	}

	/// Parse an ident
	fn parse(ttm: &TokenTreeMeta<'src>) -> Self {
		match ttm.tt {
			TokenTree::Ident(s) => Path::from_str(s, ttm.pos.clone()),
			_ => ttm.pos.error(Expected("path")),
		}
	}

	fn from_str(path_str: &'src str, pos: SrcPos<'src>) -> Self {
		let (is_absolute, path_str) = if path_str.ends_with("\\") {
			pos.error("Path ends with `\\`")
		} else if path_str.starts_with('\\') {
			if path_str.len() == 1 {
				pos.error("Path is a lone `\\`")
			}
			(true, &path_str[1..])
		} else {
			(false, path_str)
		};

		Path{
			parts: path_str.split('\\')
				.map(|part| if part == "" {
					pos.error(Invalid("path"))
				} else {
					part
				})
				.collect(),
			is_absolute: is_absolute,
			pos: pos
		}
	}
}
impl<'src> PartialEq<str> for Path<'src> {
	fn eq(&self, rhs: &str) -> bool {
		self.to_string() == rhs
	}
}

/// # Rust equivalent
///
/// `path\to\item` => `path::to::item`
/// `(path\to\module sub\item1 item2)` == `path::to::module{ sub::item1, item2 }``
/// `(lvl1::lvl2 (lvl2a lvl3a lvl3b) lvl2b)` == `use lvl1::lvl2::{ lvl2a::{ lvl3a, lvl3b}, lvl2b }`
fn parse_compound_path<'src>(ttm: &TokenTreeMeta<'src>) -> Vec<Path<'src>> {
	match ttm.tt {
		TokenTree::List(ref compound) => if let Some((chead, tail)) = compound.split_first() {
			let path_head = Path::parse(chead);
			tail.iter()
				.map(parse_compound_path)
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

#[derive(Clone, Debug)]
pub struct Use<'src> {
	pub paths: Vec<Path<'src>>,
	pub pos: SrcPos<'src>,
}
impl<'src> Use<'src> {
	fn parse(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Use<'src> {
		Use{
			paths: tts.iter().map(parse_compound_path).flat_map(|paths| paths).collect(),
			pos: pos,
		}
	}
}

#[derive(Clone, Debug)]
pub struct ConstDef<'src> {
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}

fn parse_definition<'src>(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>)
	-> (&'src str, ExprMeta<'src>)
{
	if tts.len() != 2 {
		pos.error(format!("Arity mismatch. Expected 2, found {}", tts.len()))
	} else {
		match tts[0].tt {
			TokenTree::Ident(name) => (name, ExprMeta::parse(&tts[1])),
			_ => tts[0].pos.error(Expected("identifier")),
		}
	}
}

#[derive(Clone, Debug)]
pub struct SExpr<'src> {
	pub proced: ExprMeta<'src>,
	pub args: Vec<ExprMeta<'src>>,
	pub pos: SrcPos<'src>,
}
impl<'src> SExpr<'src> {
	fn parse(proc_ttm: &TokenTreeMeta<'src>, args_tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>)
		-> Self
	{
		SExpr{
			proced: ExprMeta::parse(proc_ttm),
			args: args_tts.iter().map(ExprMeta::parse).collect(),
			pos: pos
		}
	}
}

#[derive(Clone, Debug)]
pub struct Block<'src> {
	pub uses: Vec<Use<'src>>,
	pub const_defs: HashMap<&'src str, ConstDef<'src>>,
	pub exprs: Vec<ExprMeta<'src>>,
	pub pos: SrcPos<'src>
}
impl<'src> Block<'src> {
	fn parse(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Self {
		let (uses, const_defs, exprs) = parse_items(tts);
		Block{
			uses: uses,
			const_defs: const_defs,
			exprs: exprs,
			pos: pos
		}
	}
}

#[derive(Clone, Debug)]
pub struct Cond<'src> {
	pub clauses: Vec<(ExprMeta<'src>, ExprMeta<'src>)>,
	pub else_clause: Option<ExprMeta<'src>>,
	pub pos: SrcPos<'src>,
}
impl<'src> Cond<'src> {
	fn parse(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Self {
		let mut clauses = Vec::new();
		let mut else_clause = None;

		for ttm in tts {
			match ttm.tt {
				TokenTree::List(ref clause) if clause.len() == 2 =>
					if let TokenTree::Ident("else") = clause[0].tt {
						if else_clause.is_none() {
							else_clause = Some(ExprMeta::parse(&clause[1]))
						} else {
							clause[0].pos.error("Duplicate `else` clause")
						}
					} else {
						clauses.push((ExprMeta::parse(&clause[0]), ExprMeta::parse(&clause[1])))
					},
				_ => ttm.pos.error(Expected("list")),
			}
		}
		Cond{ clauses: clauses, else_clause: else_clause, pos: pos }
	}

	/// Iterate over predicates of clauses.
	/// This excludes the else clause, since it contains no predicate
	pub fn iter_predicates_mut<'it>(&'it mut self) -> Box<Iterator<Item=&mut ExprMeta<'src>> + 'it>
	{
		Box::new(self.clauses.iter_mut().map(|&mut (ref mut p, _)| p))
	}
	/// Iterate over all clauses of self, including the else clause
	pub fn iter_consequences_mut<'it>(&'it mut self)
		-> Box<Iterator<Item=&mut ExprMeta<'src>> + 'it>
	{
		Box::new(self.clauses.iter_mut()
			.map(|&mut (_, ref mut c)| c)
			.chain(self.else_clause.iter_mut()))
	}
}

// TODO: Add support for capturing all args as a list, like `(lambda all-eq xs (for-all xs eq))`
//       for variadic expressions like `(all-eq a b c d)`
#[derive(Clone, Debug)]
pub struct Lambda<'src> {
	pub params: Vec<TypedBinding<'src>>,
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}
impl<'src> Lambda<'src> {
	fn parse(tts: &[TokenTreeMeta<'src>], pos: SrcPos<'src>) -> Self {
		if tts.len() != 2 {
			pos.error(ArityMis(2, tts.len()))
		} else {
			match tts[0].tt {
				TokenTree::List(ref params) => Lambda{
					params: params.iter().map(TypedBinding::parse).collect(),
					body: ExprMeta::parse(&tts[1]),
					pos: pos
				},
				_ => tts[0].pos.error(Expected("list")),
			}
		}
	}
}

// TODO: Separate into declaration and assignment. Let VarDecl create an l-value
#[derive(Clone, Debug)]
pub struct VarDef<'src> {
	pub binding: TypedBinding<'src>,
	pub mutable: bool,
	pub body: ExprMeta<'src>,
	pub pos: SrcPos<'src>
}

#[derive(Clone, Debug)]
pub struct Assign<'src> {
	pub lvalue: &'src str,
	pub rvalue: ExprMeta<'src>,
	pub pos: SrcPos<'src>,
}

#[derive(Clone, Debug)]
pub enum Expr<'src> {
	Nil(SrcPos<'src>),
	NumLit(&'src str, SrcPos<'src>),
	StrLit(StrLit<'src>, SrcPos<'src>),
	Bool(bool, SrcPos<'src>),
	Binding(Path<'src>),
	SExpr(SExpr<'src>),
	Block(Block<'src>),
	Cond(Cond<'src>),
	Lambda(Lambda<'src>),
	VarDef(VarDef<'src>),
	Assign(Assign<'src>),
	Symbol(&'src str, SrcPos<'src>),
}
impl<'src> Expr<'src> {
	pub fn is_var_def(&self) -> bool {
		if let &Expr::VarDef(_) = self { true } else { false }
	}

	fn pos(&self) -> &SrcPos<'src> {
		match *self {
			Expr::Nil(ref p) | Expr::Symbol(_, ref p) | Expr::NumLit(_, ref p)
				| Expr::StrLit(_, ref p) | Expr::Bool(_, ref p)
			=> p,
			Expr::Binding(ref path) => &path.pos,
			Expr::SExpr(ref sexpr) => &sexpr.pos,
			Expr::Block(ref block) => &block.pos,
			Expr::Cond(ref cond) => &cond.pos,
			Expr::Lambda(ref l) => &l.pos,
			Expr::VarDef(ref def) => &def.pos,
			Expr::Assign(ref a) => &a.pos,
		}
	}

	fn parse_quoted(ttm: &TokenTreeMeta<'src>) -> Self {
		match ttm.tt {
			TokenTree::List(ref list) => Expr::SExpr(SExpr{
				proced: ExprMeta::new(Expr::Binding(Path::from_str("list", ttm.pos.clone()))),
				args: list.iter()
					.map(|li| ExprMeta::new(Expr::parse_quoted(li)))
					.collect(),
				pos: ttm.pos.clone(),
			}),
			TokenTree::Ident(ident) => Expr::Symbol(ident, ttm.pos.clone()),
			TokenTree::Num(num) => Expr::NumLit(num, ttm.pos.clone()),
			TokenTree::Str(s) => Expr::StrLit(s, ttm.pos.clone()),
		}
	}
	pub fn parse(ttm: &TokenTreeMeta<'src>) -> Self {
		match ttm.tt {
			TokenTree::List(ref sexpr) => if let Some((head, tail)) = sexpr.split_first() {
				match head.tt {
					TokenTree::Ident("quote") => if let Some(to_quote) = tail.first() {
						Expr::parse_quoted(to_quote)
					} else {
						ttm.pos.error(ArityMis(1, sexpr.len()))
					},
					TokenTree::Ident("cond") => Expr::Cond(Cond::parse(tail, ttm.pos.clone())),
					TokenTree::Ident("lambda") =>
						Expr::Lambda(Lambda::parse(tail, ttm.pos.clone())),
					TokenTree::Ident("block") =>
						Expr::Block(Block::parse(tail, ttm.pos.clone())),
					_ => Expr::SExpr(SExpr::parse(&sexpr[0], tail, ttm.pos.clone())),
				}
			} else {
				Expr::Nil(ttm.pos.clone())
			},
			TokenTree::Ident("true") => Expr::Bool(true, ttm.pos.clone()),
			TokenTree::Ident("false") => Expr::Bool(false, ttm.pos.clone()),
			TokenTree::Ident(ident) => Expr::Binding(Path::from_str(ident, ttm.pos.clone())),
			TokenTree::Num(num) => Expr::NumLit(num, ttm.pos.clone()),
			TokenTree::Str(s) => Expr::StrLit(s, ttm.pos.clone()),
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Clone, Debug)]
pub struct ExprMeta<'src> {
	pub val: Box<Expr<'src>>,
	pub typ: Type<'src>,
	pub ty_ascription: Option<(Type<'src>, SrcPos<'src>)>,
}
impl<'src> ExprMeta<'src> {
	pub fn new(value: Expr<'src>) -> Self {
		ExprMeta{ val: Box::new(value), typ: Type::Unknown, ty_ascription: None }
	}

	pub fn new_type_ascripted(value: Expr<'src>, typ: Type<'src>, pos: SrcPos<'src>) -> Self {
		ExprMeta{ val: Box::new(value), typ: Type::Unknown, ty_ascription: Some((typ, pos)) }
	}

	pub fn pos(&self) -> &SrcPos<'src> {
		self.ty_ascription.as_ref().map(|&(_, ref pos)| pos).unwrap_or(self.val.pos())
	}

	pub fn parse(ttm: &TokenTreeMeta<'src>) -> Self {
		match ttm.tt {
			// Check for type ascription around expression, e.g. `(:F64 12)`
			TokenTree::List(ref sexpr) if sexpr.len() == 3 && sexpr[0].tt == TokenTree::Ident(":")
				=> ExprMeta::new_type_ascripted(
					Expr::parse(&sexpr[2]),
					Type::parse(&sexpr[1]),
					ttm.pos.clone()),
			TokenTree::List(ref sexpr) if sexpr.len() > 0 && sexpr[0].tt == TokenTree::Ident(":")
				=> ttm.pos.error(ArityMis(2, sexpr.len() - 1)),
			_ => ExprMeta::new(Expr::parse(ttm))
		}
	}
}

/// Parse TokenTree:s as a list of items
fn parse_items<'src>(tts: &[TokenTreeMeta<'src>])
	-> (Vec<Use<'src>>, HashMap<&'src str, ConstDef<'src>>, Vec<ExprMeta<'src>>)
{
	let (mut uses, mut const_defs, mut exprs) = (Vec::new(), HashMap::new(), Vec::new());

	for ttm in tts {
		match ttm.tt {
			TokenTree::List(ref sexpr) if ! sexpr.is_empty() => match sexpr[0].tt {
				TokenTree::Ident("use") => uses.push(Use::parse(&sexpr[1..], ttm.pos.clone())),
				TokenTree::Ident("def-const") => {
					let (ident, body) = parse_definition(&sexpr[1..], ttm.pos.clone());

					if const_defs.insert(ident, ConstDef{ body: body, pos: ttm.pos.clone() })
						.is_some()
					{
						ttm.pos.error(format!("Duplicate constant definition `{}`", ident))
					}
				},
				_ => exprs.push(ExprMeta::parse(ttm)),
			},
			_ => exprs.push(ExprMeta::parse(ttm)),
		}
	}

	(uses, const_defs, exprs)
}

#[derive(Clone, Debug)]
pub struct AST<'src> {
	pub uses: Vec<Use<'src>>,
	pub const_defs: HashMap<&'src str, ConstDef<'src>>,
}
impl<'src> AST<'src> {
	pub fn parse(tts: &[TokenTreeMeta<'src>]) -> AST<'src> {
		let (uses, const_defs, exprs) = parse_items(tts);

		for expr in exprs {
			expr.pos().error("Expression at top level");
		}

		AST{ uses: uses, const_defs: const_defs }
	}
}
