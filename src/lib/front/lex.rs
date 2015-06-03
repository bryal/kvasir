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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token<'a> {
	LParen,
	RParen,
	Ident(&'a str),
	Num(&'a str),
	Str(&'a str),
	Colon,
	Backtick,
}

fn try_tokenize<F>(src: &str, i: usize, f: F) -> (Token, usize)
	where F: Fn(&str) -> Result<(Token, usize), String>
{
	match f(&src[i..]) {
		Ok(x) => x,
		Err(e) => error_in_source_at(src, i, e)
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
			'"' => return Ok((Token::Str(&src[1..i]), i)),
			_ => (),
		}
	}
	Err("Unterminated string literal".into())
}
fn tokenize_raw_str_lit(src: &str) -> Result<(Token, usize), String> {
	// Assume first char is an 'r'
	let n_delim_octothorpes = src[1..].chars().take_while(|c| c == '#').count();

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
	let mut char_it = src.char_indices();

	for (i, c) in  {
		// TODO: Add 'E' notation, e.g. 3.14E10, 5E-4
		match c {
			'_' | _ if c.is_numeric() => (),
			'.' if !has_decimal_pt => has_decimal_pt = true,
			_ => return Ok((Token::Num(&src[..i]), i)),
		}
	}
	Err("Invalid numeric literal".into())
}
fn tokenize_ident(src: &str) -> Result<(Token, usize), String> {
	// Assume first characted has already been checked to be valid
	for (i, c) in src.char_indices() {
		match c {
			')' | ']' | '}' => return Ok((Token::Ident(&src[0..i]), i)),
			_ => (),
		}
	}
	Err("Invalid ident".into())
}

struct Tokens<'a> {
	src: &'a str,
	start_i: usize,
}
impl From<&str> for Tokens {
	fn from(src: &str) -> Tokens { Tokens{ src: src, debug_src_i: 0 } }
}
impl Iterator for Tokens {
	type Item = Token;

	fn next(&mut self) -> Option<Token> {
		let mut char_it = self.src[self.start_i..]
			.char_indices()
			.map(|(i, c)| (i + self.start_i, c));

		while let Some((i, c)) in char_it.next() {
			let (t, len) = match c {
				_ if c.is_whitespace() => continue,
				';' => {
					while let Some((_, c)) = char_it.next() {
						if c == '\n' { break; }
					}
					continue
				},
				'`' => (Token::Backtick, 1),
				':' => (Token::Colon, 1),
				'(' => (Token::LParen, 1), ')' => (Token::RParen, 1),
				'"' => try_tokenize(self.src, i, tokenize_str_lit),
				'r' if self.src[i + 1 ..].starts_with(|c: char| c == '"' || c == '#') =>
					try_tokenize(self.src, i, tokenize_raw_str_lit),
				_ if c.is_numeric() =>
					try_tokenize(self.src, i, tokenize_num_lit),
				_ => try_tokenize(self.src, i, tokenize_ident),
			};

			self.start_i = i + len;
			return Some(t);
		}
		None
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use super::Token::*;
}
