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

use super::{ find_closing_delim, parse_typed_bindings, parse_components };
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
			let result = match token {
				Token::LParen => find_closing_delim(Token::LParen, &tokens[i + 1 ..])
					.map(|delim_i| delim_i + i + 1)
					.ok_or("Cond::parse: failed to find closing paren".into())
					.and_then(|delim_i| parse_exprs(&tokens[i + 1 .. delim_i])
						.map(|expr| (expr, delim_i + 1 - i))),
				t => Err(format!("Cond::parse: unexpected token `{:?}`", t)),
			};

			if let Ok((items, used_tokens)) = result {
				if items.len() == 2 {
					let is_else = if let Expr::Binding(Ident::Name(ref b)) = *items[0].value {
						b == "else"
					} else {
						false
					};
					if is_else {
						cond.else_clause = Some(items[1].clone());

						return Ok(cond);
					}
					cond.clauses.push((items[0].clone(), items[1].clone()));
				} else {
					return Err(
						format!("Cond::parse: clause is not pair of expressions: `{:?}`", items)
					);
				}
				i += used_tokens;
			} else if let Err(e) = result {
				return Err(e);
			}
		}

		Ok(cond)
	}
}

impl Lambda {
	fn parse(tokens: &[Token]) -> Result<Lambda, String> {
		if let Some(&Token::LParen) = tokens.get(0) {
			find_closing_delim(Token::LParen, &tokens[1..])
				.map(|delim_i| delim_i + 1)
				.ok_or("Lambda::parse: failed to find closing paren".into())
				.and_then(|delim_i| parse_typed_bindings(&tokens[1..delim_i])
					.map(|binds| (binds, delim_i + 1)))
				.and_then(|(binds, body_i)| ExprMeta::parse(&tokens[body_i..])
					.map(|(body, _)| Lambda{ arg_bindings: binds, body: body }))
		} else {
			Err(format!("Lambda::parse: expected parenthesized bindings, found `{:?}`",
				tokens.get(0)
			))
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
			return Err("ExprMeta::parse: no tokens".into());
		}

		let result = match tokens[0] {
			Token::LParen => find_closing_delim(Token::LParen, &tokens[1..])
				.map(|delim_i| delim_i + 1)
				.ok_or("ExprMeta::parse: failed to find closing paren".into())
				.and_then(|delim_i| Expr::parse_parenthesized(&tokens[1..delim_i])
					.map(|expr| (expr, delim_i + 1))),
			Token::String(s) => Ok((Expr::StrLit(s.into()), 1)),
			Token::Number(n) => Ok((Expr::NumLit(n.into()), 1)),
			Token::Ident(_) => Ident::parse(tokens).map(|(ident, len)| (Expr::Binding(ident), len)),
			Token::LT => Ok((Expr::Binding(Ident::Name("<".into())), 1)),
			Token::GT => Ok((Expr::Binding(Ident::Name(">".into())), 1)),
			Token::Eq => Ok((Expr::Binding(Ident::Name("=".into())), 1)),
			Token::Exclamation => Ok((Expr::Binding(Ident::Name("!".into())), 1)),
			Token::Amp => Ok((Expr::Binding(Ident::Name("&".into())), 1)),
			t => Err(format!("ExprMeta::parse: unexpected token `{:?}`", t)),
		};

		result.and_then(|(expr, expr_len)| {
			let (maybe_type, type_len) = match tokens.get(expr_len) {
				Some(&Token::Colon) => if let Ok((ty, tl)) = Type::parse(&tokens[expr_len + 1 ..]) {
					(Some(ty), tl)
				} else {
					return Err("parse_expr: colon not followed by a type".into());
				},
				_ => (None, 0),
			};
			let tokens_used = expr_len + if type_len != 0 { 1 + type_len } else { 0 };
			Ok((ExprMeta::new(expr, maybe_type), tokens_used))
		})
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
