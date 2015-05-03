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

use super::parse_brackets;
use ast::Type;
use lex::Token;

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
