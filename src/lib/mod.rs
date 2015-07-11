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

// TODO: Error type that combines message with line, column, file, etc.

use std::iter::repeat;
use std::fmt::Debug;

pub use self::front::lex::token_trees_from_src;
pub use self::front::macro_::expand_macros;
// pub use self::back::compile;
// pub use self::ast::*;
pub use self::collections::ScopeStack;

pub mod front;
// pub mod middle;
// pub mod back;
// pub mod ast;
pub mod collections;

// TODO: Make this a macro so that it will be recognized to panic
pub fn error_in_source_at(src: &str, i: usize, e: String) {
	let mut line_start_i = 0;
	for (line_n, line) in src.lines().enumerate().map(|(n, l)| (n+1, l)) {
		let line_len = line.chars().count() + 1; // Include length of newline char

		if line_start_i <= i && i < line_start_i + line_len {
			let col = i - line_start_i;
			println!("\
					{}:{}: Error: {}\n\
					{}: {}\n\
					{}▲",
				line_n, col, e,
				line_n, line,
				repeat(' ').take(col + (line_n as f32).log10() as usize + 3).collect::<String>());
			return;
		}
		line_start_i += line_len;
	}
	panic!("error_in_source_at: Index {} not reached. `src.len()`: {}", i, src.len())
}
