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

// TODO: Maybe some kind of MaybeOwned, CowString or whatever for error messages.
// TODO: Let the custom error type be based on enum for reusable messages

use std::collections::HashMap;
use std::borrow::Cow;

use super::lex::TokenTree;
use lib::error_in_source_at;

// NOTE: A Symbol should be a wrapper around a static string reference, where
//       reference equality would imply value equality
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<'a> {
	Unknown,
	Basic(Cow<'a, str>),
	Construct(Cow<'a, str>, Vec<Type<'a>>),
	Poly(Cow<'a, str>),
}
/// The tuple has the type constructor `*`, as it is a
/// [product type](https://en.wikipedia.org/wiki/Product_type).
/// Nil is implemented as the empty tuple
impl<'a> Type<'a> {
	pub fn new_basic<S: Into<Cow<'a, str>>>(t: S) -> Self { Type::Basic(t.into()) }
	pub fn new_construct<S: Into<Cow<'a, str>>>(constructor: S, args: Vec<Type<'a>>) -> Self {
		Type::Construct(constructor.into(), args)
	}
	pub fn new_poly<S: Into<Cow<'a, str>>>(t: S) -> Self { Type::Poly(t.into()) }
	pub fn new_tuple(args: Vec<Type<'a>>) -> Self { Type::new_construct("*", args) }
	pub fn new_nil() -> Self { Type::new_tuple(vec![]) }
	pub fn new_fn(mut arg_tys: Vec<Type<'a>>, return_ty: Type<'a>) -> Self {
		arg_tys.push(return_ty);
		Type::Construct("fn".into(), arg_tys)
	}

	pub fn is_unknown(&self) -> bool {
		match self {
			&Type::Unknown => true,
			_ => false
		}
	}
	// TODO: Remake into something like `is_known`, include partial constructors etc.
	pub fn is_partly_known(&self) -> bool {
		!self.is_unknown()
	}
	pub fn is_poly(&self) -> bool {
		match self {
			&Type::Poly(_) => true,
			_ => false
		}
	}

	pub fn parse(&(ref tt, pos): &(TokenTree<'a>, usize)) -> Result<Type<'a>, (String, usize)> {
		match *tt {
			TokenTree::List(ref construct) if ! construct.is_empty() => match construct[0] {
				(TokenTree::Ident(constructor), _) => construct.tail()
					.iter()
					.map(Type::parse)
					.collect::<Result<_, _>>()
					.map(|args| Type::new_construct(constructor, args)),
				(_, c_pos) => Err(("Invalid type constructor".into(), c_pos)),
			},
			TokenTree::List(_) => Ok(Type::new_nil()),
			TokenTree::Ident(basic) => Ok(Type::new_basic(basic)),
			TokenTree::Num(num) => Err((format!("Expected type, found `{}`", num), pos)),
			TokenTree::Str(s) => Err((format!("Expected type, found `{:?}`", s), pos)),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedBinding<'a> {
	pub ident: &'a str,
	pub typ: Type<'a>,
	pos: usize,
}
impl<'a> TypedBinding<'a> {
	fn parse(&(ref tt, pos): &(TokenTree<'a>, usize)) -> Result<Self, (String, usize)> {
		match *tt {
			TokenTree::List(ref tb) if ! tb.is_empty() && tb[0].0 == TokenTree::Ident(":") =>
				if tb.len() == 3 {
					match tb[2] {
						(TokenTree::Ident(ident), _) => Type::parse(&tb[1])
							.map(|ty| TypedBinding{ ident: ident, typ: ty, pos: pos }),
						(_, bpos) => Err(("Invalid binding".into(), bpos))
					}
				} else {
					Err(("Invalid type ascription".into(), pos))
				},
			TokenTree::Ident(ident) => Ok(
				TypedBinding{ ident: ident, typ: Type::Unknown, pos: pos }),
			_ => Err(("Invalid binding".into(), pos))
		}
	}
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Path<'a> {
	parts: Vec<&'a str>,
	is_absolute: bool,
	pos: usize
}
impl<'a> Path<'a> {
	pub fn is_absolute(&self) -> bool { self.is_absolute }

	pub fn parts(&self) -> &[&str] { &self.parts }

	/// If self is just a simple ident, return it as Some
	pub fn ident(&self) -> Option<&str> {
		if ! self.is_absolute { self.parts.first().map(|&s| s) } else { None }
	}

	/// Concatenates two paths.
	/// Returns both `self` and `other` as `Err` if right hand path is absolute
	pub fn concat(mut self, other: Self) -> Result<Self, (Self, Self)> {
		if other.is_absolute {
			Err((self, other))
		} else {
			self.parts.extend(other.parts);
			Ok(self)
		}
	}

	pub fn to_string(&self) -> String {
		format!(
			"{}{}{}",
			if self.is_absolute() { "\\" } else { "" },
			self.parts[0],
			self.parts[1..].iter().fold(String::new(), |acc, p| acc + "\\" + p))
	}

	/// Parse an ident
	fn parse(&(ref tt, pos): &(TokenTree<'a>, usize)) -> Result<Self, (String, usize)> {
		match *tt {
			TokenTree::Ident(s) => Path::from_str(s, pos),
			_ => Err(("Invalid path".into(), pos)),
		}
	}

	fn from_str(path_str: &'a str, pos: usize) -> Result<Self, (String, usize)> {
		let (is_absolute, path_str) = if path_str.ends_with("\\") {
			return Err(("Path ends with `\\`".into(), pos));
		} else if path_str.starts_with('\\') {
			if path_str.len() == 1 {
				return Err(("Path is a lone `\\`".into(), pos));
			}
			(true, &path_str[1..])
		} else {
			(false, path_str)
		};

		path_str.split('\\')
			.map(|part| if part == "" {
				Err(("Invalid path".into(), pos))
			} else {
				Ok(part)
			})
			.collect::<Result<Vec<_>, _>>()
			.map(|parts| Path{ parts: parts, is_absolute: is_absolute, pos: pos })
	}
}
impl<'a> PartialEq<str> for Path<'a> {
	fn eq(&self, rhs: &str) -> bool {
		self.to_string() == rhs
	}
}

/// # Rust equivalent
///
/// `path\to\item` => `path::to::item`
/// (path\to\module sub\item1 item2) == path::to::module{ sub::item1, item2 }
/// (lvl1::lvl2 (lvl2a lvl3a lvl3b) lvl2b) == use lvl1::lvl2::{ lvl2a::{ lvl3a, lvl3b}, lvl2b }
fn parse_compound_path<'a>(&(ref tt, pos): &(TokenTree<'a>, usize))
	-> Result<Vec<Path<'a>>, (String, usize)>
{
	match *tt {
		TokenTree::List(ref compound) if ! compound.is_empty() => Path::parse(&compound[0])
			.and_then(|head| compound.tail()
				.iter()
				.map(parse_compound_path)
				.collect::<Result<Vec<_>, _>>()
				.and_then(|vs| vs.into_iter()
					.flat_map(|v| v)
					.map(|sub| head.clone()
						.concat(sub)
						.map_err(|(_, sub)|
							(format!("`{}` is absolute", sub.to_string()), sub.pos)))
					.collect::<Result<_, _>>())),
		TokenTree::List(_) => Err(("Empty path compound".into(), pos)),
		TokenTree::Ident(ident) => Path::from_str(ident, pos).map(|path| vec![path]),
		TokenTree::Num(num) => Err((format!("Expected path, found `{}`", num), pos)),
		TokenTree::Str(s) => Err((format!("Expected path, found `{:?}`", s), pos)),
	}
}

#[derive(Clone, Debug)]
pub struct Use<'a> {
	pub paths: Vec<Path<'a>>,
}
impl<'a> Use<'a> {
	fn parse(tts: &[(TokenTree<'a>, usize)]) -> Result<Use<'a>, (String, usize)> {
		tts.iter()
			.map(parse_compound_path)
			.collect::<Result<Vec<_>, _>>()
			.map(|vs| Use{
				paths: vs.into_iter().flat_map(|paths| paths).collect()
			})
	}
}

fn parse_definition<'a>(tts: &[(TokenTree<'a>, usize)], pos: usize)
	-> Result<(&'a str, Expr<'a>), (String, usize)>
{
	if tts.len() != 2 {
		Err(("`def-const` expects 2 arguments".into(), pos))
	} else {
		match tts[0] {
			(TokenTree::Ident(name), _) => Expr::parse(&tts[1]).map(|body| (name, body)),
			(_, npos) => Err(("Invalid constant name. Expected identifier".into(), npos)),
		}
	}
}

#[derive(Clone, Debug)]
pub struct SExpr<'a> {
	pub proced: Expr<'a>,
	pub args: Vec<Expr<'a>>,
	pos: usize,
}
impl<'a> SExpr<'a> {
	fn parse(proc_tt: &(TokenTree<'a>, usize), args_tts: &[(TokenTree<'a>, usize)], expr_pos: usize)
		-> Result<Self, (String, usize)>
	{
		Expr::parse(proc_tt)
			.and_then(|proced| args_tts.iter()
				.map(Expr::parse)
				.collect::<Result<_, _>>()
				.map(|args| SExpr{ proced: proced, args: args, pos: expr_pos }))
	}
}

#[derive(Clone, Debug)]
pub struct Block<'a> {
	pub uses: Vec<Use<'a>>,
	pub const_defs: HashMap<&'a str, (Expr<'a>, usize)>,
	pub exprs: Vec<Expr<'a>>,
	pos: usize
}
impl<'a> Block<'a> {
	fn parse(tts: &[(TokenTree<'a>, usize)], pos: usize) -> Result<Self, (String, usize)> {
		parse_items(tts).map(|(uses, const_defs, exprs)| Block{
			uses: uses,
			const_defs: const_defs,
			exprs: exprs,
			pos: pos
		})
	}
}

#[derive(Clone, Debug)]
pub struct Cond<'a> {
	pub clauses: Vec<(Expr<'a>, Expr<'a>)>,
	pub else_clause: Option<Expr<'a>>,
	pos: usize,
}
impl<'a> Cond<'a> {
	fn parse(tts: &[(TokenTree<'a>, usize)], pos: usize) -> Result<Self, (String, usize)> {
		let mut clauses = Vec::new();
		let mut else_clause = None;

		for &(ref tt, tt_pos) in tts {
			match *tt {
				TokenTree::List(ref clause) if clause.len() == 2 =>
					if let TokenTree::Ident("else") = clause[0].0 {
						if else_clause.is_none() {
							else_clause = Some(try!(Expr::parse(&clause[1])))
						} else {
							return Err(("Duplicate `else` clause".into(), clause[0].1))
						}
					} else {
						clauses.push((try!(Expr::parse(&clause[0])), try!(Expr::parse(&clause[1]))))
					},
				_ => return Err(("Invalid cond clause".into(), tt_pos)),
			}
		}

		Ok(Cond{ clauses: clauses, else_clause: else_clause, pos: pos })
	}
}

// TODO: Add support for capturing all args as a list, like `(lambda all-eq xs (for-all xs eq))`
//       for variadic expressions like `(all-eq a b c d)`
#[derive(Clone, Debug)]
pub struct Lambda<'a> {
	pub params: Vec<TypedBinding<'a>>,
	pub body: Expr<'a>,
	pos: usize,
}
impl<'a> Lambda<'a> {
	fn parse(tts: &[(TokenTree<'a>, usize)], pos: usize) -> Result<Self, (String, usize)> {
		if tts.len() != 2 {
			Err((format!("Arity mismatch. Expected {}, found {}", 2, tts.len()), pos))
		} else {
			match tts[0] {
				(TokenTree::List(ref params), _) => params.iter()
					.map(TypedBinding::parse)
					.collect::<Result<_, _>>()
					.and_then(|params| Expr::parse(&tts[1])
						.map(|body| Lambda{ params: params, body: body, pos: pos })),
				(_, apos) => Err(("Expected parameter list".into(), apos)),
			}
		}
	}
}

// TODO: Separate into declaration and assignment. Let VarDecl create an l-value
#[derive(Clone, Debug)]
pub struct VarDef<'a> {
	pub binding: TypedBinding<'a>,
	pub mutable: bool,
	pub body: Expr<'a>,
	pos: usize
}

#[derive(Clone, Debug)]
pub struct Assign<'a> {
	pub lvalue: &'a str,
	pub rvalue: Expr<'a>,
	pos: usize,
}

#[derive(Clone, Debug)]
pub enum ExprVariant<'a> {
	Nil(usize),
	NumLit(&'a str, usize),
	StrLit(&'a str, usize),
	Bool(&'a str, usize),
	Binding(Path<'a>),
	SExpr(SExpr<'a>),
	Block(Block<'a>),
	Cond(Cond<'a>),
	Lambda(Lambda<'a>),
	VarDef(VarDef<'a>),
	Assign(Assign<'a>),
	Symbol(&'a str, usize),
	List(Vec<Expr<'a>>, usize)
}
impl<'a> ExprVariant<'a> {
	pub fn is_var_def(&self) -> bool { if let &ExprVariant::VarDef(_) = self { true } else { false } }

	fn pos(&self) -> usize {
		match *self {
			ExprVariant::Nil(p) | ExprVariant::Symbol(_, p) | ExprVariant::NumLit(_, p)
				| ExprVariant::StrLit(_, p) | ExprVariant::Bool(_, p) | ExprVariant::List(_, p)
			=> p,
			ExprVariant::Binding(ref path) => path.pos,
			ExprVariant::SExpr(ref sexpr) => sexpr.pos,
			ExprVariant::Block(ref block) => block.pos,
			ExprVariant::Cond(ref cond) => cond.pos,
			ExprVariant::Lambda(ref l) => l.pos,
			ExprVariant::VarDef(ref def) => def.pos,
			ExprVariant::Assign(ref a) => a.pos,
		}
	}

	fn parse_quoted(&(ref tt, pos): &(TokenTree<'a>, usize)) -> Result<Self, (String, usize)> {
		match *tt {
			TokenTree::List(ref list) => list.iter()
				.map(|li| ExprVariant::parse_quoted(li).map(|e| Expr::new(e, Type::Unknown)))
				.collect::<Result<Vec<_>, _>>()
				.map(|list| ExprVariant::List(list, pos)),
			TokenTree::Ident(ident) => Ok(ExprVariant::Symbol(ident, pos)),
			TokenTree::Num(num) => Ok(ExprVariant::NumLit(num, pos)),
			TokenTree::Str(s) => Ok(ExprVariant::StrLit(s, pos)),
		}
	}
	pub fn parse(tt_and_pos: &(TokenTree<'a>, usize)) -> Result<Self, (String, usize)> {
		let pos = tt_and_pos.1;
		match tt_and_pos.0 {
			TokenTree::List(ref sexpr) if ! sexpr.is_empty() => match sexpr[0].0 {
				TokenTree::Ident("quote") if sexpr.len() == 2 =>
					ExprVariant::parse_quoted(&sexpr[1]),
				TokenTree::Ident("quote") =>
					Err(("Arity mismatch. Expected 1 argument".into(), pos)),
				TokenTree::Ident("cond") => Cond::parse(sexpr.tail(), pos).map(ExprVariant::Cond),
				TokenTree::Ident("lambda") =>
					Lambda::parse(sexpr.tail(), pos).map(ExprVariant::Lambda),
				TokenTree::Ident("block") =>
					Block::parse(sexpr.tail(), pos).map(ExprVariant::Block),
				_ => SExpr::parse(&sexpr[0], sexpr.tail(), pos).map(ExprVariant::SExpr),
			},
			TokenTree::List(_) => Ok(ExprVariant::Nil(pos)),
			TokenTree::Ident(path) => Path::parse(tt_and_pos)
				.map(|path| ExprVariant::Binding(path)),
			TokenTree::Num(num) => Ok(ExprVariant::NumLit(num, pos)),
			TokenTree::Str(s) => Ok(ExprVariant::StrLit(s, pos)),
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Clone, Debug)]
pub struct Expr<'a> {
	pub val: Box<ExprVariant<'a>>,
	pub typ: Type<'a>,
}
impl<'a> Expr<'a> {
	pub fn new(value: ExprVariant<'a>, typ: Type<'a>) -> Self {
		Expr{ val: Box::new(value), typ: typ }
	}
	// pub fn new_true() -> Expr { Expr::new(Expr::Bool(true), Type::new_basic("bool")) }
	// pub fn new_false() -> Expr { Expr::new(Expr::Bool(false), Type::new_basic("bool")) }
	// pub fn new_nil() -> Expr { Expr::new(Expr::Nil, Type::new_nil()) }

	fn pos(&self) -> usize { self.val.pos() }

	pub fn parse(tt_and_pos: &(TokenTree<'a>, usize)) -> Result<Self, (String, usize)> {
		let pos = tt_and_pos.1;
		match tt_and_pos.0 {
			// Check for type ascription around expression, e.g. `(:F64 12)`
			TokenTree::List(ref sexpr) if sexpr.len() != 0 && sexpr[0].0 == TokenTree::Ident(":") =>
				if sexpr.len() == 3 {
					Type::parse(&sexpr[1]).and_then(|ty|
						ExprVariant::parse(&sexpr[2]).map(|val|
							Expr::new(val, ty)))
				} else {
					Err(("Invalid type ascription".into(), pos))
				},
			_ => ExprVariant::parse(tt_and_pos).map(|val| Expr::new(val, Type::Unknown))
		}
	}
}

/// Parse TokenTree:s as a list of items
fn parse_items<'a>(tts: &[(TokenTree<'a>, usize)])
	-> Result<(Vec<Use<'a>>, HashMap<&'a str, (Expr<'a>, usize)>, Vec<Expr<'a>>), (String, usize)>
{
	let (mut uses, mut const_defs, mut exprs) = (Vec::new(), HashMap::new(), Vec::new());

	for tt_and_pos in tts {
		match *tt_and_pos {
			(TokenTree::List(ref sexpr), pos) if ! sexpr.is_empty() => match sexpr[0].0 {
				TokenTree::Ident("use") => uses.push(try!(Use::parse(sexpr.tail()))),
				TokenTree::Ident("def-const") => try!(parse_definition(sexpr.tail(), pos)
					.and_then(|(ident, body)| match const_defs.insert(ident, (body, pos)) {
						Some(_) => Err((format!("Duplicate constant definition `{}`", ident), pos)),
						None => Ok(()),
					})),
				_ => exprs.push(try!(Expr::parse(tt_and_pos))),
			},
			_ => exprs.push(try!(Expr::parse(tt_and_pos))),
		}
	}

	Ok((uses, const_defs, exprs))
}

#[derive(Clone, Debug)]
pub struct AST<'a> {
	pub uses: Vec<Use<'a>>,
	pub const_defs: HashMap<&'a str, (Expr<'a>, usize)>,
}
impl<'a> AST<'a> {
	pub fn parse(tts: &[(TokenTree<'a>, usize)]) -> Result<AST<'a>, (String, usize)> {
		let (uses, const_defs, exprs) = try!(parse_items(tts));

		for expr in exprs {
			return Err(("Expression at top level".into(), expr.pos()));
		}

		Ok(AST{ uses: uses, const_defs: const_defs })
	}
}

pub fn parse_ast<'a>(src: &str, tts: &[(TokenTree<'a>, usize)]) -> AST<'a> {
	match AST::parse(tts) {
		Ok(ast) => ast,
		Err((e, pos)) => panic!(error_in_source_at(src, pos, e))
	}
}
