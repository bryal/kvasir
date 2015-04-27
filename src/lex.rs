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

enum Token {
	LParen,
	RParen,
	Int(&str),
	Float(&str),
	Ident(&str),
}

/// Does not split string literals
pub fn split_by_whitespace(mut src: &str) -> Result<Vec<&str>, &'static str> {
	src = src.trim();

	let mut splits = Vec::with_capacity(src.len() / 2);

	let mut char_iterator = Box::new(src.chars().enumerate()) as Box<Iterator<Item=(usize, char)>>;
	while let Some((byte_i, _)) = char_iterator.next() {
		let from_here = &src[byte_i..];

		// `Some` if item att current index is a string literal
		let maybe_start_len_and_delim = if let Some(0) = from_here.find('"') {
			Some((1, String::from("\"")))
		} else if let Some(0) = from_here.find("r\"") {
			Some((2, String::from("\"")))
		} else if let Some(0) = from_here.find("r#") {
			from_here.find('"').and_then(|i| if from_here[1..i].bytes().all(|c| c == '#' as u8) {
				let s = String::from("\"") + &from_here[1..i];
				Some((s.len(), s))
			} else {
				None
			})
		} else {
			None
		};

		char_iterator = if let Some((start_len, str_delim)) = maybe_start_len_and_delim {
			// It's a string literal
			if let Some(end_i) = from_here[start_len..]
				.find(&str_delim)
				.map(|i| i + str_delim.len() + 1)
			{
				splits.push(&from_here[..end_i]);
				Box::new(char_iterator.skip_while(move |&(i, _)| i <= end_i + byte_i))
					as Box<Iterator<Item=_>>
			} else {
				return Err("Undelimited string literal")
			}
		} else {
			// Not a string, just split until next space
			let end_i = from_here.find(|c: char| c.is_whitespace()).unwrap_or(from_here.len());
			splits.push(&from_here[..end_i]);
			Box::new(char_iterator.skip_while(move |&(i, _)| i <= end_i + byte_i))
				as Box<Iterator<Item=_>>
		};
	}

	Ok(splits)
}

fn tokenize_word(word: &str) -> Vec<Token> {
	let mut tokens = Vec::with_capacity((word.len() * 3) / 2);

	for c in word.chars() {

	}
}

fn tokenize_string(src: &str) -> Vec<Token> {
	split_by_whitespace(src).into_iter()
		.fold(Vec::with_capacity(src.len() / 2), |acc, word| acc.extend(tokenize_word(word)))
}