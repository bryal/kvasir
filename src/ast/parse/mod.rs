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

use ast::*;
use lex::Token;

mod items;
mod types;
mod expressions;

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

	fn concat(self, other: &Path) -> Result<Path, String> {
		if other.is_absolute {
			Err(format!(
				"Path::concat: `{}` is an absolute path",
				other.to_str()))
		} else {
			Ok(Path::new(self.parts + &other.parts, self.is_absolute))
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
					Ok((ty, tl)) => (Some(ty), tl),
					Err(e) => return Err(e),
				}
			} else {
				(None, 0)
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

impl Component {
	fn parse(tokens: &[Token]) -> Result<(Component, usize), String> {
		if tokens.len() == 0 {
			return Err("Component::parse: no tokens".into());
		}

		match tokens[0] {
			Token::LParen | Token::LBracket | Token::String(_) | Token::Number(_)
			| Token::Ident(_) | Token::LT | Token::GT
				=> ExprMeta::parse(tokens).map(|(e, l)| (Component::Expr(e), l)),

			Token::LBrace => ItemMeta::parse(tokens).map(|(i, l)| (Component::Item(i), l)),

			t => Err(format!("Component::parse: unexpected token `{:?}`", t)),
		}
	}
}

/// Parse tokens as a list of components
fn parse_components(tokens: &[Token]) -> Result<(Vec<ItemMeta>, Vec<ExprMeta>), String> {
	if tokens.len() == 0 {
		return Err("parse_components: no tokens".into());
	}

	let (mut items, mut exprs) = (Vec::new(), Vec::new());

	let mut i = 0;
	while i < tokens.len() {
		match Component::parse(&tokens[i..]) {
			Ok((Component::Item(item), len)) => {
				items.push(item);
				i += len;
			},
			Ok((Component::Expr(expr), len)) => {
				exprs.push(expr);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok((items, exprs))
}

impl AST {
	pub fn parse(tokens: &[Token]) -> Result<AST, String> {
		parse_components(tokens).map(|(items, _)| AST{ items: items })
	}
}
