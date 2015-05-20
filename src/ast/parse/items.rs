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

use super::{ parse_typed_bindings, parse_brackets };
use ast::*;
use lex::Token;

// (prefix::path item1 item2) => [prefix::path::item1, prefix::path::item2]
fn parse_prefixed_paths(tokens: &[Token]) -> Result<Vec<Path>, String> {
	match Path::parse(tokens) {
		Ok(head) => parse_use_paths(&tokens[1..])
			.and_then(|tails| {
				let mut paths = Vec::new();

				for path_result in tails.into_iter().map(|tail| head.concat(tail)) {
					match path_result {
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

impl FnDef {
	fn parse(tokens: &[Token]) -> Result<FnDef, String> {
		if tokens.len() == 0 {
			Err("FnDef::parse: no tokens".into())
		} else {
			if let Token::LParen = tokens[0] {
				parse_brackets(tokens, parse_typed_bindings)
					.map(|(binds, n_used_tokens)| (binds.into_iter(), n_used_tokens))
					.and_then(|(mut binds, body_i)| ExprMeta::parse(&tokens[body_i..])
						.and_then(|(body, _)| binds.next()
							.map(|binding| FnDef{
								binding: binding,
								arg_bindings: binds.collect(),
								body: body
							})
							.ok_or(format!("FnDef::parse: no function binding given"))))
			} else {
				Err(format!("FnDef::parse: unexpected token `{:?}`", tokens[0]))
			}
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
			Token::LBrace => parse_brackets(tokens, ItemMeta::parse_braced),
			t => Err(format!("ItemMeta::parse: unexpected token `{:?}`", t)),
		}
	}

	/// Parse an expression from tokens within parentheses
	fn parse_braced(tokens: &[Token]) -> Result<ItemMeta, String> {
		if tokens.len() == 0 {
			return Err("ItemMeta::parse_braced: no tokens".into());
		}

		match tokens[0] {
			Token::Ident("use") => Use::parse(&tokens[1..]).map(|u| Item::Use(u)),
			Token::Ident("_define_fn") => FnDef::parse(&tokens[1..]).map(|f| Item::FnDef(f)),
			Token::Ident("_define_const") => ConstDef::parse(&tokens[1..])
				.map(|c| Item::ConstDef(c)),
			t => Err(format!("ItemMeta::parse: unexpected token `{:?}`", t)),
		}.map(|item| ItemMeta{ item: Box::new(item) })
	}
}
