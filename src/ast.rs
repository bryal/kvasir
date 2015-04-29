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

use lex::Token;

type Type = String;

#[derive(Debug, Clone)]
struct Lambda {
	args: Vec<(String, Option<Type>)>,
	body: ExprMeta
}

#[derive(Debug, Clone)]
struct SExpr {
	func: ExprMeta,
	args: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
enum Expr {
	Conditional(Vec<(ExprMeta, ExprMeta)>),
	SExpr(SExpr),
	NumLit(String),
	StrLit(String),
	Binding(String),
	Lambda(Lambda),
	// ArrayLit(String),
	Block(Vec<ExprMeta>),
	// Definition(),
	Nil,
}

#[derive(Debug, Clone)]
struct ExprMeta {
	value: Box<Expr>,
	coerce_type: Option<Type>
}

impl ExprMeta {
	fn new(value: Expr, coerce_type: Option<Type>) -> ExprMeta {
		ExprMeta{ value: Box::new(value), coerce_type: coerce_type }
	} 
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

fn parse_type(tokens: &[Token]) -> Option<(Type, usize)> {
	match tokens.get(0) {
		Some(&Token::Ident(s)) => Some((s.into(), 1)),
		_ => panic!("NOT YET IMPLEMENTED")
	}
}

fn parenthesized_to_expr(exprs: &[ExprMeta]) -> Result<Expr, String> {
	if exprs.len() == 0 {
		return Ok(Expr::Nil);
	}

	match *exprs[0].value {
		Expr::Binding(_) => Ok(Expr::SExpr(SExpr{
			func: exprs[0].clone(),
			args: exprs[1..].to_vec()
		})),
		_ => panic!("NOT YET IMPLEMENTED")
	}
}

// Parse the tokens until a full expresion is found.
// Return the expr and how many tokens were used for it.
fn parse_expr(tokens: &[Token]) -> Result<(ExprMeta, usize), String> {
	if tokens.len() == 0 {
		return Err("parse_expr: no tokens".into());
	}

	let result = match tokens[0] {
		Token::LParen => find_closing_delim(Token::LParen, &tokens[1..])
			.map(|delim_i| delim_i + 1)
			.ok_or("parse_exprs: failed to find closing paren".into())
			.and_then(|delim_i| parse_exprs(&tokens[1..delim_i])
				.and_then(|exprs| parenthesized_to_expr(&exprs))
				.map(|expr| (expr, delim_i + 1))
			),
		Token::RParen => Err("parse_expr: unexpected right paren".into()),
		Token::LBracket => panic!("NOT YET IMPLEMENTED"),
		Token::RBracket => Err("parse_expr: unexpected right bracket".into()),
		Token::LBrace => find_closing_delim(Token::LBrace, &tokens[1..])
			.map(|delim_i| delim_i + 1)
			.ok_or("parse_exprs: failed to find closing brace".into())
			.and_then(|delim_i| parse_exprs(&tokens[1..delim_i])
				.map(|exprs| (Expr::Block(exprs), delim_i + 1))
			),
		Token::RBrace => Err("parse_expr: unexpected right brace".into()),
		Token::String(s) => Ok((Expr::StrLit(s.into()), 1)),
		Token::Number(n) => Ok((Expr::NumLit(n.into()), 1)),
		Token::Ident(ident) => Ok((Expr::Binding(ident.into()), 1)),
		Token::LT => Ok((Expr::Binding("<".into()), 1)),
		Token::GT => Ok((Expr::Binding(">".into()), 1)),
		Token::Eq => Ok((Expr::Binding("=".into()), 1)),
		Token::Exclamation => Ok((Expr::Binding("!".into()), 1)),
		Token::Colon => Err("parse_expr: unexpected colon".into()),
	};

	
	result.map(|(expr, expr_len)| {
		let (maybe_type, type_len) = match tokens.get(expr_len) {
			Some(&Token::Colon) => parse_type(&tokens[expr_len + 1 ..])
				.map(|(t, tl)| (Some(t), tl))
				.unwrap_or((None, 0)),
			_ => (None, 0),
		};
		let tokens_used = expr_len + if type_len != 0 { 1 + type_len } else { 0 };
		(ExprMeta::new(expr, maybe_type), tokens_used)
	}) 
}

/// Parse tokens to items of some expr.
/// E.g. might be function binding and operands in a SExpr, might be clauses in a conditional
fn parse_exprs(tokens: &[Token]) -> Result<Vec<ExprMeta>, String> {
	let mut exprs = Vec::new();

	let mut i = 0;
	while i < tokens.len() {
		match parse_expr(&tokens[i..]) {
			Ok((expr, len)) => {
				exprs.push(expr);
				i += len;
			},
			Err(e) => return Err(e),
		}
	}

	Ok(exprs)
}

#[derive(Debug, Clone)]
pub struct AST {
	nodes: Vec<ExprMeta>,
}

impl AST {
	pub fn parse(tokens: &[Token]) -> Result<AST, String> {
		parse_exprs(tokens).map(|exprs| AST{ nodes: exprs })
	}
}