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

use super::{ find_closing_delim, parse_typed_bindings };
use ast::*;
use lex::Token;

// (prefix::path item1 item2) => [prefix::path::item1, prefix::path::item2]
fn parse_prefixed_paths(tokens: &[Token]) -> Result<Vec<Ident>, String> {
	match Ident::parse(tokens) {
		Ok((head, head_len)) => parse_use_paths(&tokens[head_len..])
			.map(|tails| tails.into_iter()
				.map(|tail| head.clone().concat(tail))
				.collect()),
		Err(e) => Err(e),
	}
}

fn parse_use_paths(tokens: &[Token]) -> Result<Vec<Ident>, String> {
	let mut all_paths = Vec::new();

	let mut i = 0;
	while let Some(token) = tokens.get(i) {
		match *token {
			Token::Ident(_) => match Ident::parse(&tokens[i..]) {
				Ok((path, path_len)) => {
					all_paths.push(path);
					i += path_len;
				},
				Err(e) => return Err(e)
			},
			Token::LParen => match find_closing_delim(Token::LParen, &tokens[i + 1 ..])
				.map(|delim_i| delim_i + 1)
				.ok_or("parse_use_paths: failed to find closing paren".into())
				.and_then(|delim_i| parse_prefixed_paths(&tokens[i + 1 .. delim_i])
					.map(|paths| (paths, delim_i)))
			{
				Ok((paths, delim_i)) => {
					all_paths.extend(paths);
					i = delim_i + 1;
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

impl FnDef {
	fn parse(tokens: &[Token]) -> Result<FnDef, String> {
		if let Some(&Token::LParen) = tokens.get(0) {
			find_closing_delim(Token::LParen, &tokens[1..])
				.map(|delim_i| delim_i + 1)
				.ok_or("FnDef::parse: failed to find closing paren".into())
				.and_then(|delim_i| parse_typed_bindings(&tokens[1..delim_i])
					.map(|binds| (binds.into_iter(), delim_i + 1)))
				.and_then(|(mut binds, body_i)| ExprMeta::parse(&tokens[body_i..])
					.and_then(|(body, _)| binds.next()
						.map(|binding| FnDef{
							binding: binding,
							arg_bindings: binds.collect(),
							body: body
						})
						.ok_or(format!("FnDef::parse: no function binding given"))))

		} else {
			Err(format!("FnDef::parse: expected parenthesized bindings, found `{:?}`",
				tokens.get(0)
			))
		}
	}
}

impl ConstDef {
	fn parse(tokens: &[Token]) -> Result<ConstDef, String> {
		if let Some(&Token::Ident(ident)) = tokens.get(0) {
			if let Some(&Token::Colon) = tokens.get(1) {
				Type::parse(&tokens[2..]).map(|(ty, tl)| (Some(ty), tl))
			} else {
				Ok((None, 0))
			}.and_then(|(ty, used_tokens)| {
				let body_i = 1 + if used_tokens != 0 { 1 + used_tokens } else { 0 };
				ExprMeta::parse(&tokens[body_i..]).map(|(body, _)| ConstDef{
					binding: TypedBinding{ ident: ident.into(), type_sig: ty },
					body: body
				})
			})
		} else {
			Err(format!("ConstDef::parse: unexpected token `{:?}`", tokens.get(0)))
		}
	}
}

impl ItemMeta {
	pub fn parse(tokens: &[Token]) -> Result<(ItemMeta, usize), String> {
		if tokens.len() == 0 {
			return Err("ItemMeta::parse: no tokens".into());
		}

		match tokens[0] {
			Token::LBrace => find_closing_delim(Token::LBrace, &tokens[1..])
				.map(|delim_i| delim_i + 1)
				.ok_or("ItemMeta::parse: failed to find closing brace".into())
				.and_then(|delim_i| ItemMeta::parse_braced(&tokens[1..delim_i])
					.map(|item| (ItemMeta{ item: Box::new(item) }, delim_i + 1))),
			t => Err(format!("ItemMeta::parse: unexpected token `{:?}`", t)),
		}
	}

	/// Parse an expression from tokens within parentheses
	fn parse_braced(tokens: &[Token]) -> Result<Item, String> {
		if tokens.len() == 0 {
			return Err("ItemMeta::parse_braced: no tokens".into());
		}

		match tokens[0] {
			Token::Ident("use") => Use::parse(&tokens[1..]).map(|u| Item::Use(u)),
			Token::Ident("_define_fn") => FnDef::parse(&tokens[1..]).map(|f| Item::FnDef(f)),
			Token::Ident("_define_const") => ConstDef::parse(&tokens[1..])
				.map(|c| Item::ConstDef(c)),
			t => Err(format!("ItemMeta::parse: unexpected token `{:?}`", t)),
		}
	}
}
