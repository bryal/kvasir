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

use std::fmt;

/// A position or interval in a string of source code
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct SrcPos<'src> {
	pub src: &'src str,
	pub start: usize,
	pub end: Option<usize>,
	pub in_expansion: Option<Box<SrcPos<'src>>>
}
impl<'src> SrcPos<'src> {
	/// Construct a new `SrcPos` representing a position in `src`
	fn new_pos(src: &'src str, pos: usize) -> Self {
		SrcPos{ src: src, start: pos, end: None, in_expansion: None }
	}
	/// Construct a new `SrcPos` representing an interval in `src`
	fn new_interval(src: &'src str, start: usize, end: usize) -> Self {
		SrcPos{ src: src, start: start, end: Some(end), in_expansion: None }
	}
	/// Construct a new `SrcPos` representing a position in `src` in the expansion of a macro
	fn new_pos_in_expansion(src: &'src str, pos: usize, parent: SrcPos<'src>) -> Self {
		SrcPos{ src: src, start: pos, end: None, in_expansion: Some(Box::new(parent)) }
	}
	/// Construct a new `SrcPos` representing an interval in `src` in the expansion of a macro
	fn new_interval_in_expansion(src: &'src str, start: usize, end: usize, parent: SrcPos<'src>)
		-> Self
	{
		SrcPos{ src: src, start: start, end: Some(end), in_expansion: Some(Box::new(parent)) }
	}

	pub fn add_expansion_site(&mut self, exp: &SrcPos<'src>) {
		if self.in_expansion.is_some() {
		// if let Some(ref mut self_exp) = self.in_expansion {
			// Not sure whether this should be an error
			// panic!("Internal Compiler Error: add_expansion_site: \
			//         Tried to add expansion site `{:?}` to pos `{:?}`",
			// 	exp,
			// 	self);
			// self_exp.add_expansion_site(exp);
		} else {
			self.in_expansion = Some(Box::new(exp.clone()));
		}
	}
}
impl<'src> fmt::Debug for SrcPos<'src> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		match self.end {
			Some(end) => write!(fmt, "SrcPos {{ start: {}, end: {} }}", self.start, end),
			None => write!(fmt, "SrcPos {{ start: {} }}", self.start),
		}
	}
}

/// A string literal.
///
/// Can be either a `Plain` string literal, where *escapes* such as newline, '\n',
/// can be produced using backslash, `\`, or a `Raw` string literal,
/// where escape sequences are not processed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrLit<'src> {
	Plain(&'src str),
	Raw(&'src str),
}

/// A token
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Token<'src> {
	LParen,
	RParen,
	Ident(&'src str),
	Num(&'src str),
	Str(StrLit<'src>),
	Quote,
}

/// Tokenize the string literal in `src` at `start`.
/// Return the `Token` and it's length, including delimiting characters, in the source.
///
/// # Panics
/// Panics if the string literal is unterminated
fn tokenize_str_lit(src: &str, start: usize) -> (Token, usize) {
	let str_body_src = &src[start + 1 ..];
	let mut char_it = str_body_src.char_indices();

	while let Some((i, c)) = char_it.next() {
		match c {
			// TODO: Unescape escape sequences
			// '\\' => { char_it.next(); },
			'"' => return (Token::Str(StrLit::Plain(&str_body_src[..i])), i + 2),
			_ => (),
		}
	}
	src_error_panic!(src, start, "Unterminated string literal")
}

/// Tokenize the raw string literal in `src` at `start`.
/// Return the `Token` and it's length, including delimiting characters, in the source.
///
/// # Panics
/// Panics if the raw string literal is unterminated
fn tokenize_raw_str_lit(src: &str, start: usize) -> (Token, usize) {
	let str_src = &src[start + 1 ..];
	let n_delim_octothorpes = str_src.chars().take_while(|&c| c == '#').count();

	if ! str_src[n_delim_octothorpes..].starts_with('"') {
		src_error_panic!(src, start, "Invalid raw string delimiter");
	}

	let delim_octothorpes = &str_src[..n_delim_octothorpes];

	let str_body_src = &str_src[n_delim_octothorpes + 1 ..];
	for (i, c) in str_body_src.char_indices() {
		if c == '"' && str_body_src[i + 1 ..].starts_with(delim_octothorpes) {
			// octothorpes before and after + 'r' + open and end quotes + str len
			let literal_len = n_delim_octothorpes * 2 + 3 + i;
			return (Token::Str(StrLit::Raw(&str_body_src[..i])), literal_len)
		}
	}
	src_error_panic!(src, start, "Unterminated raw string literal")
}

/// Tokenize the numeric literal in `src` at `start`.
/// Return the `Token` and it's length in the source.
///
/// # Panics
/// Panics if the literal is not a valid numeric literal
fn tokenize_num_lit(src: &str, start: usize) -> (Token, usize) {
	let src_num = &src[start..];
	let mut has_decimal_pt = false;
	let mut has_e = false;
	let mut prev_was_e = false;

	for (i, c) in src_num.char_indices() {
		match c {
			'_' => (),
			'E' if !has_e => {
				has_e = true;
				prev_was_e = true
			},
			'-' if prev_was_e => (),
			_ if c.is_numeric() => (),
			'.' if !has_decimal_pt => has_decimal_pt = true,
			_ if is_delim_char(c) => return (Token::Num(&src_num[..i]), i),
			_ => break
		}
		if c != 'E' {
			prev_was_e = false;
		}
	}
	src_error_panic!(src, start, "Invalid numeric literal")
}

/// Returns whether `c` delimits tokens
fn is_delim_char(c: char) -> bool {
	match c {
		'(' | ')' | '[' | ']' | '{' | '}' | ';' => true,
		_ if c.is_whitespace() => true,
		_ => false,
	}
}

/// Returns whether `c` is a valid character of an ident
fn is_ident_char(c: char) -> bool {
	match c {
		'\'' | ':' | '"' => false,
		_ if is_delim_char(c) => false,
		_ => true,
	}
}

/// Tokenize the numeric literal in `src` at `start`.
/// Return the `Token` and it's length in the source.
///
/// # Panics
/// Panics if the literal is not a valid numeric literal
fn tokenize_ident(src: &str, start: usize) -> (Token, usize) {
	let src_ident = &src[start..];
	for (i, c) in src_ident.char_indices() {
		if is_delim_char(c) {
			return (Token::Ident(&src_ident[..i]), i)
		} else if ! is_ident_char(c) {
			break
		}
	}
	src_error_panic!(src, start, "Invalid ident")
}

/// An iterator of `Token`s and their position in some source code
#[derive(Debug)]
struct Tokens<'src> {
	src: &'src str,
	pos: usize,
}
impl<'src> From<&'src str> for Tokens<'src> {
	fn from(src: &'src str) -> Tokens { Tokens{ src: src, pos: 0 } }
}
impl<'src> Iterator for Tokens<'src> {
	type Item = (Token<'src>, SrcPos<'src>);

	fn next(&mut self) -> Option<(Token<'src>, SrcPos<'src>)> {
		let pos = self.pos;
		let mut char_it = self.src[pos..]
			.char_indices()
			.map(|(n, c)| (pos + n, c));

		while let Some((i, c)) = char_it.next() {
			let (token, len) = match c {
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
				'"' => tokenize_str_lit(self.src, i),
				'r' if self.src[i + 1 ..].starts_with(|c: char| c == '"' || c == '#') =>
					tokenize_raw_str_lit(self.src, i),
				_ if c.is_numeric() => tokenize_num_lit(self.src, i),
				_ if is_ident_char(c) => tokenize_ident(self.src, i),
				_ => src_error_panic!(self.src, i, "Unexpected char"),
			};

			self.pos = i + len;
			return Some((token, SrcPos::new_interval(self.src, i, self.pos)));
		}
		None
	}
}

/// A tree of lists, identifiers, and literals
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenTree<'src> {
	List(Vec<TokenTreeMeta<'src>>),
	Ident(&'src str),
	Num(&'src str),
	Str(StrLit<'src>),
}
impl<'src> TokenTree<'src> {
	pub fn get_ident(&self) -> Option<&str> {
		match *self {
			TokenTree::Ident(ident) => Some(ident),
			_ => None,
		}
	}
}

/// A `TokenTree` with meta-data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenTreeMeta<'src> {
	pub tt: TokenTree<'src>,
	pub pos: SrcPos<'src>,
}
impl<'src> TokenTreeMeta<'src> {
	/// Construct a new `TokenTreeMeta` from a `TokenTree` and a source position
	pub fn new(tt: TokenTree<'src>, pos: SrcPos<'src>) -> Self {
		TokenTreeMeta{ tt: tt, pos: pos }
	}

	pub fn new_list(tts: Vec<TokenTreeMeta<'src>>, pos: SrcPos<'src>) -> Self {
		TokenTreeMeta{ tt: TokenTree::List(tts), pos: pos }
	}

	pub fn list_len(&self) -> Option<usize> {
		match self.tt {
			TokenTree::List(ref list) => Some(list.len()),
			_ => None,
		}
	}

	/// Construct a new `TokenTreeMeta` from a token with a position, and the tokens following
	fn from_token((token, mut pos): (Token<'src>, SrcPos<'src>), nexts: &mut Tokens<'src>)
		-> Self
	{
		let tt = match token {
			Token::LParen => {
				let (list, end) = tokens_to_trees_until(nexts, Some((pos.clone(), &Token::RParen)));
				pos.end = end;
				TokenTree::List(list)
			},
			Token::Ident(ident) => TokenTree::Ident(ident),
			Token::Num(num) => TokenTree::Num(num),
			Token::Str(s) => TokenTree::Str(s),
			Token::Quote => TokenTree::List(vec![
				TokenTreeMeta::new(TokenTree::Ident("quote"), pos.clone()),
				TokenTreeMeta::from_token(
					nexts.next().unwrap_or_else(|| src_error_panic!(&pos, "Free quote")),
					nexts)
			]),
			_ => src_error_panic!(pos, "Unexpected token"),
		};
		TokenTreeMeta::new(tt, pos)
	}

	pub fn add_expansion_site(&mut self, exp: &SrcPos<'src>) {
		self.pos.add_expansion_site(exp);

		if let TokenTree::List(ref mut list) = self.tt {
			for li in list {
				li.add_expansion_site(exp)
			}
		}
	}
}

/// Construct trees from `tokens` until a lone `delim` is encountered.
///
/// Returns trees and index of closing delimiter if one was supplied.
fn tokens_to_trees_until<'src>(
	tokens: &mut Tokens<'src>,
	start_and_delim: Option<(SrcPos, &Token)>
) -> (Vec<TokenTreeMeta<'src>>, Option<usize>) {
	let (start, delim) = start_and_delim.map(|(s, t)| (Some(s), Some(t)))
		.unwrap_or((None, None));

	let mut tts = Vec::new();

	while let Some((token, t_pos)) = tokens.next() {
		if Some(&token) == delim {
			return (tts, t_pos.end)
		} else {
			tts.push(TokenTreeMeta::from_token((token, t_pos), tokens))
		}
	}
	match start {
		None => (tts, None),
		Some(pos) => src_error_panic!(pos, "Undelimited item"),
	}
}

/// Represent some source code as `TokenTreeMeta`s
pub fn token_trees_from_src(src: &str) -> Vec<TokenTreeMeta> {
	tokens_to_trees_until(&mut Tokens::from(src), None).0
}

#[cfg(test)]
mod test {
	use super::*;
	use super::Token::*;
}
