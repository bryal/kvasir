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

// TODO: Maybe instead of having special cases while parsing, parse all parens equaly and handle
//       special cases later separately

// TODO: Maybe some kind of MaybeOwned, CowString or whatever for error messages.

use std::collections::HashMap;
use lib::{ Path, Use, Type, TypedBinding };
use super::*;
use self::ast::{ MacroPattern, MacroRules, SExpr, Block, Cond, Lambda, Expr };
pub use self::ast::AST;

mod ast;

fn find_closing_delim(open_token: Token, tokens: &[Token]) -> Option<usize> {
	let delim = match open_token {
		Token::LParen => Token::RParen,
		Token::LBracket => Token::RBracket,
		Token::LBrace => Token::RBrace,
		_ => return None,
	};

	let mut opens = 0u64;
	for (i, token) in tokens.iter().enumerate() {
		if *token == open_token {
			opens += 1;
		} else if *token == delim {
			if opens == 0 {
				return Some(i)
			}
			opens -= 1;
		}
	}
	None
}

/// Parse content within brackets using provided function.
///
/// Return parsed content and num of used tokens. The type of bracket is denoted by the first token.
fn parse_brackets<F, T>(tokens: &[Token], content_parser: F) -> Result<(T, usize), String>
	where F: Fn(&[Token]) -> Result<T, String>
{
	find_closing_delim(tokens[0], tokens.tail())
		.map(|delim_i| delim_i + 1)
		.ok_or("parse_brackets: failed to find closing paren".into())
		.and_then(|delim_i| content_parser(&tokens[1..delim_i])
			.map(|paths| (paths, delim_i + 1)))
}

impl Type {
	/// Parse construct type from tokens assumed to be within angle brackets
	fn parse_construct(tokens: &[Token]) -> Result<Type, String> {
		if tokens.len() == 0 {
			return Err("Type::parse_construct: no tokens".into())
		}
		match tokens[0] {
			Token::Ident(ident) => parse_types(tokens.tail())
				.map(|tys| Type::Construct(ident.into(), tys)),
			t => Err(format!("Type::parse_construct: unexpected token `{:?}`", t))
		}
	}

	/// Parse tuple type from tokens assumed to be within parentheses
	fn parse_tuple(tokens: &[Token]) -> Result<Type, String> {
		parse_types(tokens).map(|tys| Type::Tuple(tys))
	}

	/// Parse a type from tokens. On success, return parsed type and number of tokens used
	pub fn parse(tokens: &[Token]) -> Result<(Type, usize), String> {
		tokens.get(0).ok_or("Type::parse: no tokens".into()).and_then(|&token| match token {
			Token::Ident("_") => Ok((Type::Inferred, 1)),
			Token::Ident(ident) => Ok((Type::Basic(ident.into()), 1)),
			Token::LBrace => parse_brackets(tokens, Type::parse_construct),
			Token::LParen => parse_brackets(tokens, Type::parse_tuple),
			t => Err(format!("Type::parse: unexpected token `{:?}`", t))
		})
	}
}

fn parse_types(tokens: &[Token]) -> Result<Vec<Type>, String> {
	let mut tys = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match Type::parse(&tokens[i..]) {
			Ok((ty, len)) => {
				tys.push(ty);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok(tys)
}

impl TypedBinding {
	fn parse_parenthesized(tokens: &[Token]) -> Result<TypedBinding, String> {
		if tokens.len() == 0 {
			Err("TypedBinding::parse_parenthesized: No tokens".into())
		} else {
			if let Token::Colon = tokens[0] {
				// Type ascription
				Type::parse(tokens.tail())
					.and_then(|(ty, len)| if tokens.tail().len() - len != 1 {
						Err("TypedBinding::parse_parenthesized: \
							Type ascription not followed by single ident".into())
					} else if let Token::Ident(ident) = tokens.tail()[len] {
						Ok(TypedBinding{ ident: ident.into(), type_sig: ty })
					} else {
						Err("TypedBinding::parse_parenthesized: \
							Type ascription not followed by ident".into())
					})
			} else {
				Err("TypedBinding::parse_parenthesized: First token is not colon".into())
			}
		}
	}

	fn parse(tokens: &[Token]) -> Result<(TypedBinding, usize), String> {
		if tokens.len() == 0 {
			Err("TypedBinding::parse: No tokens".into())
		} else {
			match tokens[0] {
				Token::LParen => parse_brackets(tokens, TypedBinding::parse_parenthesized),
				Token::Ident(ident) => Ok((TypedBinding{
						ident: ident.into(),
						type_sig: Type::Inferred
					},
					1)),
				t => Err(format!("TypedBinding::parse: Unexpected token `{:?}`", t))
			}
		}
	}
}

fn parse_typed_bindings(tokens: &[Token]) -> Result<Vec<TypedBinding>, String> {
	let mut bindings = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		let (binding, binding_len) = try!(TypedBinding::parse(&tokens[i..]));

		bindings.push(binding);

		i += binding_len;
	}

	Ok(bindings)
}

impl Path {
	/// Parse an ident
	fn parse(tokens: &[Token]) -> Result<Path, String> {
		if tokens.len() == 0 {
			return Err("Ident::parse: no tokens".into());
		}
		match tokens[0] {
			Token::Ident(s) => Path::parse_str(s),
			t => Err(format!("Ident::parse: unexpexted token `{:?}`", t)),
		}
	}

	fn parse_str(path_s: &str) -> Result<Path, String> {
		let (is_absolute, path_s) = if path_s.starts_with('\\') {
			if path_s.len() == 1 {
				return Err("Ident::parse_str: Path is a lone `\\`".into());
			} else {
				(true, &path_s[1..])
			}
		} else {
			(false, path_s)
		};

		if path_s.ends_with("\\") {
			return Err("Path::parse_str: Path ends with `\\`".into());
		}

		let mut parts = Vec::new();

		for part in path_s.split('\\') {
			if part == "" {
				return Err(format!("Path::parse_str: Invalid path `{}`", path_s));
			}
			parts.push(part.into());
		}

		Ok(Path::new(parts, is_absolute))
	}
}

fn parse_macro_patterns(tokens: &[Token]) -> Result<Vec<MacroPattern>, String> {
	let mut patterns = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		let (pat, len) = try!(MacroPattern::parse(&tokens[i..]));
		patterns.push(pat);
		i += len;
	}
	Ok(patterns)
}

impl MacroPattern {
	fn parse(tokens: &[Token]) -> Result<(MacroPattern, usize), String> {
		if tokens.len() == 0 {
			Err("MacroPattern::parse: No tokens".into())
		} else {
			match tokens[0] {
				Token::LParen => parse_brackets(tokens, parse_macro_patterns)
					.map(|(patterns, len)| (MacroPattern::List(patterns), len)),
				Token::Ident(ident) => Ok((MacroPattern::Ident(ident.into()), 1)),
				ref t => Err(format!("MacroPattern::parse: Unexpected token `{:?}`", t)),
			}
		}
	}
}

fn parse_macro_rule(tokens: &[Token]) -> Result<(MacroPattern, Expr), String> {
	MacroPattern::parse(tokens).and_then(|(pat, len)|
		// TODO: Should parse as if quoted
		Expr::parse(&tokens[len..]).map(|(expr, _)| (pat, expr)))
}

fn parse_macro_rules(tokens: &[Token]) -> Result<Vec<(MacroPattern, Expr)>, String> {
	let mut macro_rules = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match tokens[i] {
			Token::LParen => {
				let (rule, len) = try!(parse_brackets(&tokens[i..], parse_macro_rule));
				macro_rules.push(rule);
				i += len;
			},
			ref t => return Err(format!("parse_macro_rules: Unexpected token `{:?}`", t)),
		}
	}
	Ok(macro_rules)
}

impl MacroRules {
	fn parse(tokens: &[Token]) -> Result<MacroRules, String> {
		if tokens.len() == 0 {
			return Err("MacroRules::parse: No tokens".into())
		}
		match tokens[0] {
			Token::LParen => parse_brackets(tokens, |tokens| {
					let mut lits = Vec::new();
					for token in tokens {
						match token {
							&Token::Ident(ident) => lits.push(ident.into()),
							t => return Err(format!(
								"MacroRules::parse: In parse_brackets, unexpected token `{:?}`",
								t)),
						}
					}
					Ok(lits)
				})
				.and_then(|(literal_idents, len)| parse_macro_rules(&tokens[len..])
					.map(|rules| MacroRules{ literal_idents: literal_idents, rules: rules })),
			ref t => Err(format!("MacroRules::parse: Unexpected token `{:?}`", t))
		}
	}
}

fn parse_macro_def(tokens: &[Token]) -> Result<(String, MacroRules), String> {
	if tokens.len() == 0 {
		Err("parse_macro_def: No tokens".into())
	} else {
		match tokens[0] {
			Token::Ident(ident) => MacroRules::parse(tokens.tail())
				.map(|macro_rules| (ident.into(), macro_rules)),
			t => Err(format!("parse_macro_def: Expected ident, found `{:?}`", t))
		}
	}
}

// (prefix::path item1 item2) => [prefix::path::item1, prefix::path::item2]
fn parse_prefixed_paths(tokens: &[Token]) -> Result<Vec<Path>, String> {
	match Path::parse(tokens) {
		Ok(head) => parse_use_paths(tokens.tail())
			.and_then(|tails| {
				let mut paths = Vec::new();

				for tail in tails.into_iter() {
					match head.clone().concat(tail) {
						Err(e) => return Err(e),
						Ok(o) => paths.push(o),
					}
				}

				Ok(paths)
			}),
		Err(e) => Err(e),
	}
}

impl Use {
	// (use path\to\item} == use path::to::item;
	// (use (path\to\module sub\item1 item2)) == use path::to::module{ sub::item1, item2 }
	fn parse(tokens: &[Token]) -> Result<Use, String> {
		if tokens.len() == 0 {
			return Err("Use::parse: no tokens".into());
		}

		parse_use_paths(tokens).map(|paths| Use{ paths: paths })
	}
}

fn parse_use_paths(tokens: &[Token]) -> Result<Vec<Path>, String> {
	let mut all_paths = Vec::new();

	let mut i = 0;
	while let Some(token) = tokens.get(i) {
		match *token {
			Token::Ident(_) => match Path::parse(&tokens[i..]) {
				Ok(path) => {
					all_paths.push(path);
					i += 1;
				},
				Err(e) => return Err(e)
			},
			Token::LParen => match parse_brackets(tokens, parse_prefixed_paths) {
				Ok((paths, n_used_tokens)) => {
					all_paths.extend(paths);
					i += n_used_tokens;
				},
				Err(e) => return Err(e)
			},
			t => return Err(format!("parse_use_paths: unexpected token `{:?}`", t))
		}
	}

	Ok(all_paths)
}

fn parse_definition(tokens: &[Token]) -> Result<(String, Expr), String> {
	if tokens.len() == 0 {
		Err("parse_definition: No tokens".into())
	} else {
		match tokens[0] {
			Token::Ident(ident) => Expr::parse(tokens.tail())
				.and_then(|(body, body_len)| if body_len == tokens.tail().len() {
					Ok((ident.into(), body))
				} else {
					Err("parse_definition: Tokens remained after parsing body".into())
				}),
			t => Err(format!("parse_definition: Expected ident, found `{:?}`", t))
		}
	}
}

impl SExpr {
	fn parse(tokens: &[Token]) -> Result<SExpr, String> {
		parse_exprs(tokens).map(|exprs| SExpr{ func: exprs[0].clone(), args: exprs[1..].to_vec() })
	}
}

impl Block {
	fn parse(tokens: &[Token]) -> Result<Block, String> {
		parse_items(tokens).map(|items| {
			let (macro_defs, uses, const_defs, exprs) = extract_items(items);
			Block{
				macro_defs: macro_defs,
				uses: uses,
				const_defs: const_defs,
				exprs: exprs
			}
		})
	}
}

impl Cond {
	fn parse(tokens: &[Token]) -> Result<Cond, String> {
		if tokens.len() == 0 {
			return Err("Cond::parse: no tokens".into());
		}

		let mut cond = Cond{ clauses: Vec::new(), else_clause: None };

		let mut i = 0;
		while let Some(&token) = tokens.get(i) {
			if let Token::LParen = token {
				match parse_brackets(&tokens[i..], parse_exprs) {
					Ok((exprs, n_tokens)) => if exprs.len() == 2 {
						if let Expr::Binding(ref path) = exprs[0] {
							if path == "else" {
								cond.else_clause = Some(exprs[1].clone());
								return Ok(cond);
							}
						}
						cond.clauses.push((exprs[0].clone(), exprs[1].clone()));
						i += n_tokens;
					} else {
						return Err(format!(
							"Cond::parse: clause is not a pair of expressions: `{:?}`",
							exprs));
					},
					Err(e) => return Err(e)
				}
			} else {
				return Err(format!("Cond::parse: unexpected token `{:?}`", token));
			}
		}

		Ok(cond)
	}
}

impl Lambda {
	fn parse(tokens: &[Token]) -> Result<Lambda, String> {
		if tokens.len() == 0 {
			Err("Lambda::parse: no tokens".into())
		} else {
			if let Token::LParen = tokens[0] {
				parse_brackets(tokens, parse_typed_bindings)
					.and_then(|(binds, body_i)| Expr::parse(&tokens[body_i..])
						.map(|(body, _)| Lambda{ arg_bindings: binds, body: body }))
			} else {
				Err(format!("Lambda::parse: unexpected token `{:?}`", tokens[0]))
			}
		}
	}
}

/// Parse tokens as a list of expressions
fn parse_exprs(tokens: &[Token]) -> Result<Vec<Expr>, String> {
	if tokens.len() == 0 {
		return Err("parse_exprs: no tokens".into());
	}

	let mut exprs = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match Expr::parse(&tokens[i..]) {
			Ok((expr, len)) => {
				exprs.push(expr);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok(exprs)
}

impl Expr {
	/// Parse an expression from tokens within parentheses
	fn parse_parenthesized(tokens: &[Token]) -> Result<Expr, String> {
		if tokens.len() == 0 {
			return Ok(Expr::Nil);
		}

		// Handle special forms
		match tokens[0] {
			// Type ascription. `(:TYPE EXPR)`
			Token::Colon => Type::parse(tokens.tail())
				.and_then(|(ty, len)| Expr::parse(&tokens.tail()[len..])
					.map(|(expr, _)| Expr::TypeAscr(ty, Box::new(expr)))),
			Token::Ident("cond") =>
				Cond::parse(tokens.tail()).map(|c| Expr::Cond(Box::new(c))),
			Token::Ident("lambda") =>
				Lambda::parse(tokens.tail()).map(|λ| Expr::Lambda(Box::new(λ))),
			Token::Ident("block") =>
				Block::parse(tokens.tail()).map(|block| Expr::Block(Box::new(block))),
			_ => SExpr::parse(tokens).map(|se| Expr::SExpr(Box::new(se))),
		}
	}

	pub fn parse(tokens: &[Token]) -> Result<(Expr, usize), String> {
		if tokens.len() == 0 {
			Err("Expr::parse: No tokens".into())
		} else {
			match tokens[0] {
				Token::LParen => parse_brackets(tokens, Expr::parse_parenthesized),
				Token::String(s) => Ok((Expr::StrLit(s.into()), 1)),
				Token::Number(n) => Ok((Expr::NumLit(n.into()), 1)),
				Token::Ident(_) => Path::parse(tokens).map(|ident| (Expr::Binding(ident), 1)),
				t => Err(format!("Expr::parse: unexpected token `{:?}`", t)),
			}
		}
	}
}

#[derive(Debug)]
pub enum Item {
	MacroDef((String, MacroRules)),
	Use(Use),
	ConstDef((String, Expr)),
	Expr(Expr),
}
impl Item {
	/// Parse an expression from tokens within parentheses
	fn parse_parenthesized(tokens: &[Token]) -> Result<Item, String> {
		if tokens.len() == 0 {
			return Ok(Item::Expr(Expr::Nil));
		}

		match tokens[0] {
			Token::Ident("def-const") =>
				parse_definition(tokens.tail()).map(|d| Item::ConstDef(d)),
			Token::Ident("def-macro-rules") =>
				parse_macro_def(tokens.tail()).map(|d| Item::MacroDef(d)),
			Token::Ident("use") => Use::parse(tokens.tail()).map(|u| Item::Use(u)),
			_ => Expr::parse_parenthesized(tokens).map(|e| Item::Expr(e)),
		}
	}

	fn parse(tokens: &[Token]) -> Result<(Item, usize), String> {
		if tokens.len() == 0 {
			return Err("Item::parse: no tokens".into());
		}

		match tokens[0] {
			Token::LParen => parse_brackets(tokens, Item::parse_parenthesized),
			_ => Expr::parse(tokens).map(|(e, len)| (Item::Expr(e), len)),
		}
	}
}

/// Parse tokens as a list of items
fn parse_items(tokens: &[Token]) -> Result<Vec<Item>, String> {
	if tokens.len() == 0 {
		return Err("parse_items: no tokens".into());
	}

	let mut items = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match Item::parse(&tokens[i..]) {
			Ok((item, len)) => {
				items.push(item);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok(items)
}

fn extract_items(items: Vec<Item>)
	-> (HashMap<String, MacroRules>, Vec<Use>, HashMap<String, Expr>, Vec<Expr>)
{
	let (mut macro_defs, mut uses, mut const_defs, mut exprs)
		= (HashMap::new(), Vec::new(), HashMap::new(), Vec::new());

	for item in items {
		match item {
			Item::MacroDef((name, m)) => if let Some(_) = macro_defs.insert(name, m) {
				panic!("extract_items: Macro already exists in map")
			},
			Item::Use(u) => uses.push(u),
			Item::ConstDef((name, val)) => match const_defs.insert(name, val) {
				None => (),
				Some(_) => panic!("extract_items: Constant already exists in map"),
			},
			Item::Expr(e) => exprs.push(e),
		}
	}

	(macro_defs, uses, const_defs, exprs)
}

impl AST {
	pub fn parse(tokens: &[Token]) -> Result<AST, String> {
		Block::parse(tokens).map(|block| AST{ block: block })
	}
}
