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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
	LParen,
	RParen,
	LBracket,
	RBracket,
	LT,
	GT,
	Ident(&'a str),
	Number(&'a str),
	String(&'a str),
	Exclamation,
	Colon,
}

/// Split code string by whitespace. Preserve whitespace in string literals
pub fn split_by_whitespace(mut src: &str) -> Result<Vec<&str>, &'static str> {
	src = src.trim();

	let mut splits = Vec::with_capacity(src.len() / 2);

	let mut char_iter = src.char_indices();
	while let Some((byte_i, c)) = char_iter.next() {
		if c.is_whitespace() {
			continue;
		}

		let from_here = &src[byte_i..];

		// `Some` if item att current index is a string literal
		let maybe_start_len_and_delim = if let Some(0) = from_here.find('"') {
			Some((1, String::from("\"")))
		} else if let Some(0) = from_here.find("r\"") {
			Some((2, String::from("\"")))
		} else if let Some(0) = from_here.find("r#") {
			from_here.find('"').and_then(|i| if from_here[1..i].bytes().all(|c| c == '#' as u8) {
				let s = String::from("\"") + &from_here[1..i];
				Some((s.len() + 1, s))
			} else {
				None
			})
		} else {
			None
		};

		if let Some((start_len, str_delim)) = maybe_start_len_and_delim {
			// It's a string literal
			if let Some(end_i) = from_here[start_len..]
				.find(&str_delim)
				.map(|i| i + start_len + str_delim.len())
			{
				splits.push(&from_here[..end_i]);

				src = &src[byte_i + end_i ..];
				char_iter = src.char_indices();
			} else {
				return Err("Undelimited string literal")
			}
		} else {
			// Not a string, just split until next space
			let end_i = from_here.find(|c: char| c.is_whitespace()).unwrap_or(from_here.len());
			splits.push(&from_here[..end_i]);

			src = &src[byte_i + end_i ..];
			char_iter = src.char_indices();
		}
	}

	Ok(splits)
}

fn is_ident_char(c: char) -> bool {
	match c {
		'_' => true,
		'?' => true,
		c if c.is_alphanumeric() => true,
		_ => false,
	}
}

/// Tokenize a whitespace-less string of code (except in string literals)
fn tokenize_word(mut word: &str) -> Result<Vec<Token>, String> {
	if word.starts_with('"') || word.starts_with(r#"r""#) || word.starts_with("r#") {
		// The word is a string
		return Ok(vec![Token::String(word)]);
	} 

	let mut tokens = Vec::with_capacity((word.len() * 3) / 2);

	while let Some(c) = word.chars().next() {
		let shift = match c {
			'(' => { tokens.push(Token::LParen); 1 },
			')' => { tokens.push(Token::RParen); 1 },
			'[' => { tokens.push(Token::LBracket); 1 },
			']' => { tokens.push(Token::RBracket); 1 },
			'<' => { tokens.push(Token::LT); 1 },
			'>' => { tokens.push(Token::GT); 1 },
			':' => { tokens.push(Token::Colon); 1 },
			'!' => { tokens.push(Token::Exclamation); 1 },
			c if c.is_numeric() => {
				let end_pos = word.find(|c: char| !c.is_numeric() && c != '.' && c != '_')
					.unwrap_or(word.len());
				tokens.push(Token::Number(&word[..end_pos]));

				end_pos
			},
			c if is_ident_char(c) => {
				let end_pos = word.find(|c: char| !is_ident_char(c)).unwrap_or(word.len());
				tokens.push(Token::Ident(&word[..end_pos]));

				end_pos
			},
			c => return Err(format!("Unexpected character `{}`", c))
		};
		word = &word[shift..];
	}

	Ok(tokens)
}

/// Tokenize any string of code
pub fn tokenize_string(src: &str) -> Result<Vec<Token>, String> {
	match split_by_whitespace(src) {
		Ok(words) => {
			let mut out_tokens = Vec::with_capacity(src.len() / 2);
			for word in words {
				match tokenize_word(word) {
					Ok(tokens) => out_tokens.extend(tokens),
					Err(e) => return Err(e)
				}
			}
			Ok(out_tokens)
		},
		Err(e) => Err(e.into())
	}
}

#[test]
fn test_split_by_whitespace() {
	let src = r##"(foo _Bar r"b a " r#"s 1 4"# 4_100.125: Xyz"##;
	assert_eq!(&split_by_whitespace(src).unwrap(), &[
		"(foo", "_Bar", r#"r"b a ""#, r##"r#"s 1 4"#"##, "4_100.125:", "Xyz"
	]);
}

#[test]
fn test_tokenize_word() {
	use lex::Token::*;

	let src = "(4_100.125!)";
	assert_eq!(&tokenize_word(src).unwrap(), &[
		LParen, Number("4_100.125"), Exclamation, RParen
	]);
}

#[test]
fn test_tokenize_string() {
	use lex::Token::*;

	let src = r##"(f00 _Bar r"b a " r#"s 1 4"# 4_100.125: Xyz"##;
	assert_eq!(&tokenize_string(src).unwrap(), &[
		LParen,
		Ident("f00"),
		Ident("_Bar"),
		String(r#"r"b a ""#),
		String(r##"r#"s 1 4"#"##),
		Number("4_100.125"),
		Colon,
		Ident("Xyz")
	]);

	let src = r#"[foo?::<T> _bar_)"#;
	assert_eq!(&tokenize_string(src).unwrap(), &[
		LBracket, Ident("foo?"), Colon, Colon, LT, Ident("T"), GT, Ident("_bar_"), RParen
	]);
}