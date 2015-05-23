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

use ast::*;
use lex::Token;

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
		let (is_absolute, path_s) = if path_s.starts_with('/') {
			if path_s.len() == 1 {
				return Err("Ident::parse_str: Path is a lone `/`".into());
			} else {
				(true, &path_s[1..])
			}
		} else {
			(false, path_s)
		};

		if path_s.ends_with("/") {
			return Err("Path::parse_str: Path ends with `/`".into());
		}

		let mut parts = Vec::new();

		for part in path_s.split('/') {
			if part == "" {
				return Err(format!("Path::parse_str: Invalid path `{}`", path_s));
			}
			parts.push(part.into());
		}

		Ok(Path::new(parts, is_absolute))
	}

	fn concat(mut self, other: Path) -> Result<Path, String> {
		if other.is_absolute {
			Err(format!(
				"Path::concat: `{}` is an absolute path",
				other.to_str()))
		} else {
			self.parts.extend(other.parts);
			Ok(self)
		}
	}
}

impl Type {
	/// Parse construct type from tokens assumed to be within angle brackets
	fn parse_construct(tokens: &[Token]) -> Result<Type, String> {
		if tokens.len() == 0 {
			return Err("Type::parse_construct: no tokens".into())
		}
		match tokens[0] {
			Token::Ident(ident) => parse_types(&tokens[1..])
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
			Token::LT => parse_brackets(tokens, Type::parse_construct),
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

// (prefix::path item1 item2) => [prefix::path::item1, prefix::path::item2]
fn parse_prefixed_paths(tokens: &[Token]) -> Result<Vec<Path>, String> {
	match Path::parse(tokens) {
		Ok(head) => parse_use_paths(&tokens[1..])
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

impl Use {
	// {use path::to::item} == use path::to::item;
	// {use (path::to::module sub::item1 item2)} == use path::to::module{ sub::item1, item2 }
	fn parse(tokens: &[Token]) -> Result<Use, String> {
		if tokens.len() == 0 {
			return Err("Use::parse: no tokens".into());
		}

		parse_use_paths(tokens).map(|paths| Use{ paths: paths })
	}
}

impl ConstDef {
	fn parse(tokens: &[Token]) -> Result<ConstDef, String> {
		if tokens.len() == 0 {
			Err("ConstDef::parse: No tokens".into())
		} else {
			TypedBinding::parse(tokens).and_then(|(bnd, bnd_len)|
				ExprMeta::parse(&tokens[bnd_len..])
					.and_then(|(body, body_len)| if body_len + bnd_len == tokens.len() {
						Ok(ConstDef{ binding: bnd, body: body })
					} else {
						Err("ConstDef::parse: Tokens remained after parsing body".into())
					}))
		}
	}
}

fn parse_typed_bindings(tokens: &[Token]) -> Result<Vec<TypedBinding>, String> {
	let mut bindings = Vec::new();

	let mut i = 0;
	while let Some(&token) = tokens.get(i) {
		if let Token::Ident(ident) = token {
			let (type_sig, type_len) = if let Some(&Token::Colon) = tokens.get(i + 1) {
				match Type::parse(&tokens[i + 2 ..]) {
					Ok((ty, tl)) => (ty, tl),
					Err(e) => return Err(e),
				}
			} else {
				(Type::Inferred, 0)
			};

			bindings.push(TypedBinding{ ident: ident.into(), type_sig: type_sig });
			i += 1 + if type_len != 0 { 1 + type_len } else { 0 }; // (ident + colon) + type_len
		} else {
			return Err(format!("parse_typed_bindings: unexpected token `{:?}`", token));
		}
	}

	Ok(bindings)
}

fn find_closing_delim(open_token: Token, tokens: &[Token]) -> Option<usize> {
	let delim = match open_token {
		Token::LParen => Token::RParen,
		Token::LBracket => Token::RBracket,
		Token::LBrace => Token::RBrace,
		Token::LT => Token::GT,
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
	find_closing_delim(tokens[0], &tokens[1..])
		.map(|delim_i| delim_i + 1)
		.ok_or("parse_brackets: failed to find closing paren".into())
		.and_then(|delim_i| content_parser(&tokens[1..delim_i])
			.map(|paths| (paths, delim_i + 1)))
}

impl SExpr {
	fn parse(tokens: &[Token]) -> Result<SExpr, String> {
		parse_exprs(tokens).map(|exprs| SExpr{ func: exprs[0].clone(), args: exprs[1..].to_vec() })
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
						if let Expr::Binding(ref path) = *exprs[0].value {
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
					.and_then(|(binds, body_i)| ExprMeta::parse(&tokens[body_i..])
						.map(|(body, _)| Lambda{ arg_bindings: binds, body: body }))
			} else {
				Err(format!("Lambda::parse: unexpected token `{:?}`", tokens[0]))
			}
		}
	}
}

fn extract_items(items: Vec<Item>) -> (Vec<Use>, Vec<ConstDef>, Vec<ExprMeta>) {
	let (mut uses, mut const_defs, mut exprs) = (Vec::new(), Vec::new(), Vec::new());

	for item in items {
		match item {
			Item::Use(u) => uses.push(u),
			Item::ConstDef(d) => const_defs.push(d),
			Item::Expr(e) => exprs.push(e),
		}
	}

	(uses, const_defs, exprs)
}

impl Expr {
	/// Parse an expression from tokens within parentheses
	fn parse_parenthesized(tokens: &[Token]) -> Result<Expr, String> {
		if tokens.len() == 0 {
			return Ok(Expr::Nil);
		}

		match tokens[0] {
			Token::Ident("cond") => Cond::parse(&tokens[1..]).map(|c| Expr::Cond(c)),
			Token::Ident("lambda") => Lambda::parse(&tokens[1..]).map(|λ| Expr::Lambda(λ)),
			Token::Ident("block") => parse_items(&tokens[1..]).map(|items| {
				let (uses, const_defs, exprs) = extract_items(items);
				Expr::Block(Block{ uses: uses, const_defs: const_defs, exprs: exprs })
			}),
			_ => SExpr::parse(tokens).map(|se| Expr::SExpr(se)),
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
				Token::LT => Ok((Expr::Binding(Path::parse_str("<").unwrap()), 1)),
				Token::GT => Ok((Expr::Binding(Path::parse_str(">").unwrap()), 1)),
				t => Err(format!("ExprMeta::parse: unexpected token `{:?}`", t)),
			}
		}
	}
}

impl ExprMeta {
	fn parse_parenthesized(tokens: &[Token]) -> Result<ExprMeta, String> {
		if tokens.len() > 0 && tokens[0] == Token::Colon {
			// Type ascription
			Type::parse(tokens.tail())
				.and_then(|(ty, len)| Expr::parse(&tokens.tail()[len..])
					.map(|(expr, _)| ExprMeta::new(expr, ty)))
		} else {
			Expr::parse_parenthesized(tokens).map(|e| ExprMeta::new(e, Type::Inferred))
		}
	}

	pub fn parse(tokens: &[Token]) -> Result<(ExprMeta, usize), String> {
		if tokens.len() == 0 {
			Err("ExprMeta::parse: no tokens".into())
		} else {
			match tokens[0] {
				Token::LParen => parse_brackets(tokens, ExprMeta::parse_parenthesized),
				_ => Expr::parse(tokens)
					.map(|(expr, n_tokens)| (ExprMeta::new(expr, Type::Inferred), n_tokens)),
			}
		}
	}
}

/// Parse tokens as a list of expressions
fn parse_exprs(tokens: &[Token]) -> Result<Vec<ExprMeta>, String> {
	if tokens.len() == 0 {
		return Err("parse_exprs: no tokens".into());
	}

	let mut exprs = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match ExprMeta::parse(&tokens[i..]) {
			Ok((expr, len)) => {
				exprs.push(expr);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok(exprs)
}

impl Item {
	/// Parse an expression from tokens within parentheses
	fn parse_parenthesized(tokens: &[Token]) -> Result<Item, String> {
		if tokens.len() == 0 {
			return Ok(Item::Expr(ExprMeta::nil()));
		}

		let tail = &tokens.tail();

		match tokens[0] {
			Token::Ident("--def-const") => ConstDef::parse(tail).map(|d| Item::ConstDef(d)),
			Token::Ident("use") => Use::parse(tail).map(|u| Item::Use(u)),
			_ => ExprMeta::parse_parenthesized(tokens).map(|e| Item::Expr(e)),
		}
	}

	fn parse(tokens: &[Token]) -> Result<(Item, usize), String> {
		if tokens.len() == 0 {
			return Err("Item::parse: no tokens".into());
		}

		match tokens[0] {
			Token::LParen => parse_brackets(tokens, Item::parse_parenthesized),
			_ => ExprMeta::parse(tokens).map(|(e, len)| (Item::Expr(e), len)),
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

impl AST {
	pub fn parse(tokens: &[Token]) -> Result<AST, String> {
		parse_items(tokens).and_then(|items| {
			let mut ast = AST{ uses: Vec::new(), const_defs: Vec::new() };
			for item in items {
				match item {
					Item::Use(u) => ast.uses.push(u),
					Item::ConstDef(d) => ast.const_defs.push(d),
					_ => return Err(format!("AST::parse: Unexpected item `{:?}`", item)),
				}
			}

			Ok(ast)
		})
	}
}
