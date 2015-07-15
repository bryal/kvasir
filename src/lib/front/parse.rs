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

use super::lex::{ StrLit, TokenTree, TokenTreeMeta, SrcPos };

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

	pub fn parse(ttm: &TokenTreeMeta<'a>) -> Type<'a> {
		match ttm.tt {
			TokenTree::List(ref construct) if ! construct.is_empty() => match construct[0].tt {
				TokenTree::Ident(constructor) => Type::new_construct(
					constructor,
					construct.tail().iter().map(Type::parse).collect()),
				_ => src_error_panic!(&construct[0].pos, "Invalid type constructor"),
			},
			TokenTree::List(_) => Type::new_nil(),
			TokenTree::Ident(basic) => Type::new_basic(basic),
			TokenTree::Num(num) => src_error_panic!(&ttm.pos, "Expected type"),
			TokenTree::Str(s) => src_error_panic!(&ttm.pos, "Expected type"),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedBinding<'a> {
	pub ident: &'a str,
	pub typ: Type<'a>,
	pos: SrcPos<'a>,
}
impl<'a> TypedBinding<'a> {
	fn parse(ttm: &TokenTreeMeta<'a>) -> Self {
		match ttm.tt {
			TokenTree::List(ref tb) if ! tb.is_empty() && tb[0].tt == TokenTree::Ident(":") =>
				if tb.len() == 3 {
					match tb[2].tt {
						TokenTree::Ident(ident) => TypedBinding{
							ident: ident,
							typ: Type::parse(&tb[1]),
							pos: ttm.pos.clone()
						},
						_ => src_error_panic!(&tb[2].pos, "Invalid binding"),
					}
				} else {
					src_error_panic!(&ttm.pos, "Invalid type ascription")
				},
			TokenTree::Ident(ident) =>
				TypedBinding{ ident: ident, typ: Type::Unknown, pos: ttm.pos.clone() },
			_ => src_error_panic!(&ttm.pos, "Invalid binding")
		}
	}
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Path<'a> {
	parts: Vec<&'a str>,
	is_absolute: bool,
	pos: SrcPos<'a>
}
impl<'a> Path<'a> {
	pub fn is_absolute(&self) -> bool { self.is_absolute }

	pub fn parts(&self) -> &[&str] { &self.parts }

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
	fn parse(ttm: &TokenTreeMeta<'a>) -> Self {
		match ttm.tt {
			TokenTree::Ident(s) => Path::from_str(s, ttm.pos.clone()),
			_ => src_error_panic!(&ttm.pos, "Expected path"),
		}
	}

	fn from_str(path_str: &'a str, pos: SrcPos<'a>) -> Self {
		let (is_absolute, path_str) = if path_str.ends_with("\\") {
			src_error_panic!(&pos, "Path ends with `\\`")
		} else if path_str.starts_with('\\') {
			if path_str.len() == 1 {
				src_error_panic!(&pos, "Path is a lone `\\`")
			}
			(true, &path_str[1..])
		} else {
			(false, path_str)
		};

		Path{
			parts: path_str.split('\\')
				.map(|part| if part == "" {
					src_error_panic!(&pos, "Invalid path")
				} else {
					part
				})
				.collect(),
			is_absolute: is_absolute,
			pos: pos
		}
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
/// `(path\to\module sub\item1 item2)` == `path::to::module{ sub::item1, item2 }``
/// `(lvl1::lvl2 (lvl2a lvl3a lvl3b) lvl2b)` == `use lvl1::lvl2::{ lvl2a::{ lvl3a, lvl3b}, lvl2b }`
fn parse_compound_path<'a>(ttm: &TokenTreeMeta<'a>) -> Vec<Path<'a>> {
	match ttm.tt {
		TokenTree::List(ref compound) if ! compound.is_empty() => {
			let head = Path::parse(&compound[0]);
			compound.tail()
				.iter()
				.map(parse_compound_path)
				.flat_map(|v| v)
				.map(|sub| head.clone()
					.concat(&sub)
					.unwrap_or_else(|_| src_error_panic!(&sub.pos, "Sub-path is absolute")))
				.collect()
		},
		TokenTree::List(_) => src_error_panic!(&ttm.pos, "Empty path compound"),
		TokenTree::Ident(ident) => vec![Path::from_str(ident, ttm.pos.clone())],
		TokenTree::Num(_) | TokenTree::Str(_) => src_error_panic!(&ttm.pos, "Expected path"),
	}
}

#[derive(Clone, Debug)]
pub struct Use<'a> {
	pub paths: Vec<Path<'a>>,
	pos: SrcPos<'a>,
}
impl<'a> Use<'a> {
	fn parse(tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>) -> Use<'a> {
		Use{
			paths: tts.iter().map(parse_compound_path).flat_map(|paths| paths).collect(),
			pos: pos,
		}
	}
}

#[derive(Clone, Debug)]
pub struct ConstDef<'a> {
	body: ExprMeta<'a>,
	pos: SrcPos<'a>,
}

fn parse_definition<'a>(tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>) -> (&'a str, ExprMeta<'a>) {
	if tts.len() != 2 {
		src_error_panic!(&pos, format!("Arity mismatch. Expected 2, found {}", tts.len()))
	} else {
		match tts[0].tt {
			TokenTree::Ident(name) => (name, ExprMeta::parse(&tts[1])),
			_ => src_error_panic!(&tts[0].pos, "Expected identifier"),
		}
	}
}

#[derive(Clone, Debug)]
pub struct SExpr<'a> {
	pub proced: ExprMeta<'a>,
	pub args: Vec<ExprMeta<'a>>,
	pos: SrcPos<'a>,
}
impl<'a> SExpr<'a> {
	fn parse(proc_ttm: &TokenTreeMeta<'a>, args_tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>)
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
pub struct Block<'a> {
	pub uses: Vec<Use<'a>>,
	pub const_defs: HashMap<&'a str, ConstDef<'a>>,
	pub exprs: Vec<ExprMeta<'a>>,
	pos: SrcPos<'a>
}
impl<'a> Block<'a> {
	fn parse(tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>) -> Self {
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
pub struct Cond<'a> {
	pub clauses: Vec<(ExprMeta<'a>, ExprMeta<'a>)>,
	pub else_clause: Option<ExprMeta<'a>>,
	pos: SrcPos<'a>,
}
impl<'a> Cond<'a> {
	fn parse(tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>) -> Self {
		let mut clauses = Vec::new();
		let mut else_clause = None;

		for ttm in tts {
			match ttm.tt {
				TokenTree::List(ref clause) if clause.len() == 2 =>
					if let TokenTree::Ident("else") = clause[0].tt {
						if else_clause.is_none() {
							else_clause = Some(ExprMeta::parse(&clause[1]))
						} else {
							src_error_panic!(&clause[0].pos, "Duplicate `else` clause")
						}
					} else {
						clauses.push((ExprMeta::parse(&clause[0]), ExprMeta::parse(&clause[1])))
					},
				_ => src_error_panic!(&ttm.pos, "Expected list"),
			}
		}
		Cond{ clauses: clauses, else_clause: else_clause, pos: pos }
	}
}

// TODO: Add support for capturing all args as a list, like `(lambda all-eq xs (for-all xs eq))`
//       for variadic expressions like `(all-eq a b c d)`
#[derive(Clone, Debug)]
pub struct Lambda<'a> {
	pub params: Vec<TypedBinding<'a>>,
	pub body: ExprMeta<'a>,
	pos: SrcPos<'a>,
}
impl<'a> Lambda<'a> {
	fn parse(tts: &[TokenTreeMeta<'a>], pos: SrcPos<'a>) -> Self {
		if tts.len() != 2 {
			src_error_panic!(&pos, format!("Arity mismatch. Expected 2, found {}", tts.len()))
		} else {
			match tts[0].tt {
				TokenTree::List(ref params) => Lambda{
					params: params.iter().map(TypedBinding::parse).collect(),
					body: ExprMeta::parse(&tts[1]),
					pos: pos
				},
				_ => src_error_panic!(&tts[0].pos, "Expected list"),
			}
		}
	}
}

// TODO: Separate into declaration and assignment. Let VarDecl create an l-value
#[derive(Clone, Debug)]
pub struct VarDef<'a> {
	pub binding: TypedBinding<'a>,
	pub mutable: bool,
	pub body: ExprMeta<'a>,
	pos: SrcPos<'a>
}

#[derive(Clone, Debug)]
pub struct Assign<'a> {
	pub lvalue: &'a str,
	pub rvalue: ExprMeta<'a>,
	pos: SrcPos<'a>,
}

#[derive(Clone, Debug)]
pub enum Expr<'a> {
	Nil(SrcPos<'a>),
	NumLit(&'a str, SrcPos<'a>),
	StrLit(StrLit<'a>, SrcPos<'a>),
	Bool(&'a str, SrcPos<'a>),
	Binding(Path<'a>),
	SExpr(SExpr<'a>),
	Block(Block<'a>),
	Cond(Cond<'a>),
	Lambda(Lambda<'a>),
	VarDef(VarDef<'a>),
	Assign(Assign<'a>),
	Symbol(&'a str, SrcPos<'a>),
	List(Vec<ExprMeta<'a>>, SrcPos<'a>)
}
impl<'a> Expr<'a> {
	pub fn is_var_def(&self) -> bool {
		if let &Expr::VarDef(_) = self { true } else { false }
	}

	fn pos(&self) -> &SrcPos<'a> {
		match *self {
			Expr::Nil(ref p) | Expr::Symbol(_, ref p) | Expr::NumLit(_, ref p)
				| Expr::StrLit(_, ref p) | Expr::Bool(_, ref p) | Expr::List(_, ref p)
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

	fn parse_quoted(ttm: &TokenTreeMeta<'a>) -> Self {
		match ttm.tt {
			TokenTree::List(ref list) => Expr::List(
				list.iter()
					.map(|li| ExprMeta::new(Expr::parse_quoted(li), Type::Unknown))
					.collect(),
				ttm.pos.clone()),
			TokenTree::Ident(ident) => Expr::Symbol(ident, ttm.pos.clone()),
			TokenTree::Num(num) => Expr::NumLit(num, ttm.pos.clone()),
			TokenTree::Str(s) => Expr::StrLit(s, ttm.pos.clone()),
		}
	}
	pub fn parse(ttm: &TokenTreeMeta<'a>) -> Self {
		match ttm.tt {
			TokenTree::List(ref sexpr) if ! sexpr.is_empty() => match sexpr[0].tt {
				TokenTree::Ident("quote") if sexpr.len() == 2 => Expr::parse_quoted(&sexpr[1]),
				TokenTree::Ident("quote") => src_error_panic!(
					&ttm.pos,
					format!("Arity mismatch. Expected 1, found {}", sexpr.len())),
				TokenTree::Ident("cond") => Expr::Cond(Cond::parse(sexpr.tail(), ttm.pos.clone())),
				TokenTree::Ident("lambda") =>
					Expr::Lambda(Lambda::parse(sexpr.tail(), ttm.pos.clone())),
				TokenTree::Ident("block") =>
					Expr::Block(Block::parse(sexpr.tail(), ttm.pos.clone())),
				_ => Expr::SExpr(SExpr::parse(&sexpr[0], sexpr.tail(), ttm.pos.clone())),
			},
			TokenTree::List(_) => Expr::Nil(ttm.pos.clone()),
			TokenTree::Ident(path) => Expr::Binding(Path::parse(ttm)),
			TokenTree::Num(num) => Expr::NumLit(num, ttm.pos.clone()),
			TokenTree::Str(s) => Expr::StrLit(s, ttm.pos.clone()),
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Clone, Debug)]
pub struct ExprMeta<'a> {
	pub val: Box<Expr<'a>>,
	pub typ: Type<'a>,
}
impl<'a> ExprMeta<'a> {
	pub fn new(value: Expr<'a>, typ: Type<'a>) -> Self {
		ExprMeta{ val: Box::new(value), typ: typ }
	}
	// pub fn new_true() -> Expr { Expr::new(Expr::Bool(true), Type::new_basic("bool")) }
	// pub fn new_false() -> Expr { Expr::new(Expr::Bool(false), Type::new_basic("bool")) }
	// pub fn new_nil() -> Expr { Expr::new(Expr::Nil, Type::new_nil()) }

	fn pos(&self) -> &SrcPos<'a> { self.val.pos() }

	pub fn parse(ttm: &TokenTreeMeta<'a>) -> Self {
		match ttm.tt {
			// Check for type ascription around expression, e.g. `(:F64 12)`
			TokenTree::List(ref sexpr) if sexpr.len() == 3 && sexpr[0].tt == TokenTree::Ident(":")
				=> ExprMeta::new(Expr::parse(&sexpr[2]), Type::parse(&sexpr[1])),
			TokenTree::List(ref sexpr) if sexpr.len() > 0 && sexpr[0].tt == TokenTree::Ident(":")
				=> src_error_panic!(
					&ttm.pos,
					format!("Arity mismatch. Expected 2, found {}", sexpr.len() - 1)),
			_ => ExprMeta::new(Expr::parse(ttm), Type::Unknown)
		}
	}
}

/// Parse TokenTree:s as a list of items
fn parse_items<'a>(tts: &[TokenTreeMeta<'a>])
	-> (Vec<Use<'a>>, HashMap<&'a str, ConstDef<'a>>, Vec<ExprMeta<'a>>)
{
	let (mut uses, mut const_defs, mut exprs) = (Vec::new(), HashMap::new(), Vec::new());

	for ttm in tts {
		match ttm.tt {
			TokenTree::List(ref sexpr) if ! sexpr.is_empty() => match sexpr[0].tt {
				TokenTree::Ident("use") => uses.push(Use::parse(sexpr.tail(), ttm.pos.clone())),
				TokenTree::Ident("def-const") => {
					let (ident, body) = parse_definition(sexpr.tail(), ttm.pos.clone());

					if const_defs.insert(ident, ConstDef{ body: body, pos: ttm.pos.clone() })
						.is_some()
					{
						src_error_panic!(
							&ttm.pos,
							format!("Duplicate constant definition `{}`", ident))
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
pub struct AST<'a> {
	pub uses: Vec<Use<'a>>,
	pub const_defs: HashMap<&'a str, ConstDef<'a>>,
}
impl<'a> AST<'a> {
	pub fn parse(tts: &[TokenTreeMeta<'a>]) -> AST<'a> {
		let (uses, const_defs, exprs) = parse_items(tts);

		for expr in exprs {
			src_error_panic!(expr.pos(), "Expression at top level");
		}

		AST{ uses: uses, const_defs: const_defs }
	}
}
