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

use super::{ parse_typed_bindings, parse_components, parse_brackets };
use ast::*;
use lex::Token;

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

impl Expr {
	/// Parse an expression from tokens within parentheses
	fn parse_parenthesized(tokens: &[Token]) -> Result<Expr, String> {
		if tokens.len() == 0 {
			return Ok(Expr::Nil);
		}

		match tokens[0] {
			Token::Ident("cond") => Cond::parse(&tokens[1..]).map(|c| Expr::Cond(c)),
			Token::Ident("lambda") => Lambda::parse(&tokens[1..]).map(|λ| Expr::Lambda(λ)),
			Token::Ident("block") => parse_components(&tokens[1..])
				.map(|(items, exprs)| Expr::Block(Block{ items: items, exprs: exprs })),
			_ => SExpr::parse(tokens).map(|se| Expr::SExpr(se)),
		}
	}
}

impl ExprMeta {
	pub fn parse(tokens: &[Token]) -> Result<(ExprMeta, usize), String> {
		if tokens.len() == 0 {
			Err("ExprMeta::parse: no tokens".into())
		} else {
			match tokens[0] {
				// FIXME: Ident::parse should be used here
				Token::LParen => parse_brackets(tokens, Expr::parse_parenthesized),
				Token::String(s) => Ok((Expr::StrLit(s.into()), 1)),
				Token::Number(n) => Ok((Expr::NumLit(n.into()), 1)),
				Token::Ident(_) => Path::parse(tokens)
					.map(|ident| (Expr::Binding(ident), 1)),
				Token::LT => Ok((Expr::Binding(Path::parse_str("<").unwrap()), 1)),
				Token::GT => Ok((Expr::Binding(Path::parse_str(">").unwrap()), 1)),
				t => Err(format!("ExprMeta::parse: unexpected token `{:?}`", t)),
			}.and_then(|(expr, n_tokens)| {
				if n_tokens >= tokens.len() || tokens[n_tokens] != Token::Colon {
					Ok((ExprMeta::new(expr, None), n_tokens))
				} else {
					Type::parse(&tokens[n_tokens + 1 ..]).map(|(ty, tylen)|
						(ExprMeta::new(expr, Some(ty)), n_tokens + 1 + tylen))
				}
			})
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
