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

use lib::error_in_source_at;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Token<'a> {
	LParen,
	RParen,
	Ident(&'a str),
	Num(&'a str),
	Str(&'a str),
	Quote,
}

fn try_tokenize<F>(src: &str, i: usize, f: F) -> (Token, usize)
	where F: Fn(&str) -> Result<(Token, usize), String>
{
	match f(&src[i..]) {
		Ok(x) => x,
		Err(e) => panic!(error_in_source_at(src, i, e))
	}
}

fn tokenize_str_lit(src: &str) -> Result<(Token, usize), String> {
	// Assume first char is a double quote
	let mut char_it = src.char_indices();
	char_it.next();

	while let Some((i, c)) = char_it.next() {
		match c {
			'\\' => { char_it.next(); },
			// TODO: Unescape
			'"' => return Ok((Token::Str(&src[1..i]), i + 1)),
			_ => (),
		}
	}
	Err("Unterminated string literal".into())
}
fn tokenize_raw_str_lit(src: &str) -> Result<(Token, usize), String> {
	// Assume first char is an 'r'
	let n_delim_octothorpes = src[1..].chars().take_while(|&c| c == '#').count();

	let delim_octothorpes = &src[1 .. 1 + n_delim_octothorpes];

	let mut char_it = src.char_indices();
	char_it.next();

	while let Some((i, c)) = char_it.next() {
		if c == '"' && src[i + 1 ..].starts_with(delim_octothorpes) {
			return Ok((Token::Str(&src[2 + n_delim_octothorpes .. i]), i + 1))
		}
	}
	Err("Unterminated raw string literal".into())
}
fn tokenize_num_lit(src: &str) -> Result<(Token, usize), String> {
	let mut has_decimal_pt = false;
	let mut has_e = false;
	let mut prev_was_e = false;

	for (i, c) in src.char_indices() {
		// TODO: Add 'E' notation, e.g. 3.14E10, 5E-4
		match c {
			'_' => (),
			'E' if !has_e => {
				has_e = true;
				prev_was_e = true
			},
			'-' if prev_was_e => (),
			_ if c.is_numeric() => (),
			'.' if !has_decimal_pt => has_decimal_pt = true,
			_ if is_delim_char(c) => return Ok((Token::Num(&src[..i]), i)),
			_ => break
		}
		if c != 'E' {
			prev_was_e = false;
		}
	}
	Err("Invalid numeric literal".into())
}

fn is_delim_char(c: char) -> bool {
	match c {
		'(' | ')' | '[' | ']' | '{' | '}' | ';' => true,
		_ if c.is_whitespace() => true,
		_ => false,
	}
}

fn is_ident_char(c: char) -> bool {
	match c {
		'\'' | ':' | '"' => false,
		_ if is_delim_char(c) => false,
		_ => true,
	}
}
fn tokenize_ident(src: &str) -> Result<(Token, usize), String> {
	// Assume first characted has already been checked to be valid
	for (i, c) in src.char_indices() {
		if is_delim_char(c) {
			return Ok((Token::Ident(&src[0..i]), i))
		} else if !is_ident_char(c) {
			break
		}
	}
	Err("Invalid ident".into())
}

#[derive(Debug)]
struct Tokens<'a> {
	src: &'a str,
	start_i: usize,
}
impl<'a> From<&'a str> for Tokens<'a> {
	fn from(src: &'a str) -> Tokens { Tokens{ src: src, start_i: 0 } }
}
impl<'a> Iterator for Tokens<'a> {
	type Item = (Token<'a>, usize);

	fn next(&mut self) -> Option<(Token<'a>, usize)> {
		let start_i = self.start_i;
		let mut char_it = self.src[start_i..]
			.char_indices()
			.map(|(i, c)| (i + start_i, c));

		while let Some((i, c)) = char_it.next() {
			let (t, len) = match c {
				_ if c.is_whitespace() => continue,
				';' => {
					while let Some((_, c)) = char_it.next() {
						if c == '\n' { break; }
					}
					continue
				},
				'\'' => (Token::Quote, 1),
				':' => (Token::Ident(":"), 1),
				'(' => (Token::LParen, 1),
				')' => (Token::RParen, 1),
				'"' => try_tokenize(self.src, i, tokenize_str_lit),
				'r' if self.src[i + 1 ..].starts_with(|c: char| c == '"' || c == '#') =>
					try_tokenize(self.src, i, tokenize_raw_str_lit),
				_ if c.is_numeric() =>
					try_tokenize(self.src, i, tokenize_num_lit),
				_ if is_ident_char(c) => try_tokenize(self.src, i, tokenize_ident),
				_ => panic!(error_in_source_at(self.src, i, format!("Unexpected char `{}`", c))),
			};

			self.start_i = i + len;
			return Some((t, i));
		}
		None
	}
}

#[derive(Debug, Clone)]
pub enum TokenTree<'a> {
	List(Vec<(TokenTree<'a>, usize)>),
	Ident(&'a str),
	Num(&'a str),
	Str(&'a str),
}
impl<'a> TokenTree<'a> {
	fn from_token(token: Token<'a>, nexts: &mut Tokens<'a>) -> Result<TokenTree<'a>, String> {
		match token {
			Token::LParen => tokens_to_trees_until(nexts, Some(&Token::RParen))
				.map(|list| TokenTree::List(list)),
			Token::Ident(ident) => Ok(TokenTree::Ident(ident)),
			Token::Num(num) => Ok(TokenTree::Num(num)),
			Token::Str(s) => Ok(TokenTree::Str(s)),
			Token::Quote => nexts.next()
				.ok_or("Free quote".into())
				.and_then(|(next, next_pos)| TokenTree::from_token(next, nexts)
					.map(|quoted| TokenTree::List(vec![
						(TokenTree::Ident("quote"), next_pos - 1),
						(quoted, next_pos)
					]))),
			t => Err(format!("Unexpected token `{:?}`", t)),
		}
	}
}

fn tokens_to_trees_until<'a>(tokens: &mut Tokens<'a>, delim: Option<&Token>)
	-> Result<Vec<(TokenTree<'a>, usize)>, String>
{
	let mut tts = Vec::new();

	while let Some((token, t_pos)) = tokens.next() {
		match token {
			_ if Some(&token) == delim => return Ok(tts),
			_ => match TokenTree::from_token(token, tokens) {
				Ok(tt) => tts.push((tt, t_pos)),
				Err(e) => panic!(error_in_source_at(tokens.src, t_pos, e)),
			},
		}
	}
	match delim {
		None => Ok(tts),
		Some(t) => Err(format!("Undelimited item. No closing `{:?}` found", t))
	}
}

pub fn token_trees_from_src(src: &str) -> Vec<(TokenTree, usize)> {
	let mut tokens = Tokens::from(src);
	match tokens_to_trees_until(&mut tokens, None) {
		Ok(tts) => tts,
		Err(e) => panic!(error_in_source_at(src, 0, e))
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use super::Token::*;
}
