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

impl Ident {
	/// Parse an ident
	fn parse(tokens: &[Token]) -> Result<(Ident, usize), String> {
		if tokens.len() == 0 {
			return Err("Ident::parse: no tokens".into());
		}
		if let Token::Ident(head) = tokens[0] {
			if (tokens.get(1), tokens.get(2)) == (Some(&Token::Colon), Some(&Token::Colon)) {
				if let Ok((tail, n_tail_tokens)) = Ident::parse(&tokens[3..]) {
					Ok((Ident::Path(head.into(), Box::new(tail)), 3 + n_tail_tokens))
				} else {
					Err("Ident::parse: two colons were not followed by ident".into())
				}
			} else {
				Ok((Ident::Name(head.into()), 1))
			}
		} else {
			Err("Ident::parse: first token is not an ident".into())
		}
	}

	fn concat(self, other: Ident) -> Ident {
		match self {
			Ident::Name(name) => Ident::Path(name, Box::new(other)),
			Ident::Path(name, box path) => Ident::Path(name, Box::new(path.concat(other))),
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
			| Token::Ident(_) | Token::LT | Token::GT | Token::Eq | Token::Exclamation | Token::Amp
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
