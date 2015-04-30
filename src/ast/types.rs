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

use super::find_closing_delim;
use lex::Token;

#[derive(Debug, Clone)]
pub enum Type {
	Nil,
	Basic(String),
	Construct(String, Vec<Type>),
}
impl Type {
	/// Parse a type from tokens. On success, return parsed type and number of tokens used
	pub fn parse(tokens: &[Token]) -> Result<(Type, usize), String> {
		if tokens.len() == 0 {
			return Err("Type::parse: no tokens".into())
		}
		match &tokens[0] {
			&Token::Ident("Nil") => Ok((Type::Nil, 1)),
			&Token::Ident(s) => Ok((Type::Basic(s.into()), 1)),
			&Token::LT if tokens.len() > 2 => if let Token::Ident(ident) = tokens[1] {
				find_closing_delim(Token::LT, &tokens[2..])
					.map(|delim_i| delim_i + 2)
					.ok_or("Type::parse: failed to find closing angle bracket".into())
					.and_then(|delim_i| parse_types(&tokens[2..delim_i])
						.map(|tys| (Type::Construct(ident.into(), tys), delim_i + 1)))
			} else {
				Err(format!(
					"Type::parse: first token in angle brackets was not type ident: `{:?}`",
					tokens[1]
				))
			},
			_ => Err(format!("Type::parse: no valid type siganture in tokens: {:?}", tokens))
		}
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