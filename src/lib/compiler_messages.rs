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

use std::fmt::Display;

pub use lib::front::lex::SrcPos;
pub use term;

pub fn line_len_row_col<'a>(pos: &SrcPos<'a>) -> (&'a str, usize, usize, usize) {
	let mut line_start = 0;

	for (row, line) in pos.src.lines().enumerate().map(|(n, line)| (n+1, line)) {
		let line_len = line.len() + 1; // Include length of newline char

		if line_start <= pos.start && pos.start < line_start + line_len {
			let col = pos.start - line_start;

			return (line, line_len, row, col);
		}
		line_start += line_len;
	}
	panic!("Internal compiler error: line_len_row_col: Pos {:?} not reached. src.len(): {}",
		pos,
		pos.src.len())
}

pub fn in_expansion(pos: &SrcPos, t: &mut Box<term::StdoutTerminal>) {
	if let Some(ref exp) = pos.in_expansion {
		in_expansion(exp, t);
	}

	let (line, line_len, row, col) = line_len_row_col(pos);

	print!("{}:{}: ", row, col);
	t.fg(term::color::BRIGHT_MAGENTA).unwrap();
	println!("In expansion");
	t.reset().unwrap();
	println!("{}: {}", row, line);
	t.fg(term::color::BRIGHT_MAGENTA).unwrap();
	println!("{}^{}",
		::std::iter::repeat(' ').take(col + (row as f32).log10() as usize + 3)
			.collect::<String>(),
		::std::iter::repeat('~')
			.take(::std::cmp::min(
				pos.end.unwrap_or(pos.start + 1) - pos.start - 1,
				line_len - col))
			.collect::<String>()
	);
	t.reset().unwrap();
}

/// Print an error together with information regarding position in source and panic.
macro_rules! src_error_panic {
	($src:expr, $pos:expr, $msg:expr) => {
		src_error_panic!(SrcPos::new_pos($src, $pos), $msg)
	};
	($pos:expr, $msg:expr) => {{
		use lib::compiler_messages::*;

		let pos = $pos;
		let (line, line_len, row, col) = line_len_row_col(&pos);
		let mut t = term::stdout().expect("Could not acquire access to stdout");

		if let Some(ref exp) = pos.in_expansion {
			in_expansion(exp, &mut t);
		}

		print!("{}:{}: ", row, col);
		t.fg(term::color::BRIGHT_RED).unwrap();
		print!("Error: ");
		t.reset().unwrap();
		println!("{}", $msg);
		println!("{}: {}", row, line);
		t.fg(term::color::BRIGHT_RED).unwrap();
		println!("{}^{}",
			::std::iter::repeat(' ').take(col + (row as f32).log10() as usize + 3)
				.collect::<String>(),
			::std::iter::repeat('~')
				.take(::std::cmp::min(
					pos.end.unwrap_or(pos.start + 1) - pos.start - 1,
					line_len - col))
				.collect::<String>()
		);
		t.reset().unwrap();

		println!("\nError occured. Terminating compilation.\n");
		::std::process::exit(0);
	}};
}

pub fn src_warning_print<'a, S: Display>(pos: &SrcPos<'a>, msg: S) {
	let (line, line_len, row, col) = line_len_row_col(&pos);
	let mut t = term::stdout().expect("Could not acquire access to stdout");

	if let Some(ref exp) = pos.in_expansion {
		in_expansion(exp, &mut t);
	}

	print!("{}:{}: ", row, col);
	t.fg(term::color::BRIGHT_YELLOW).unwrap();
	print!("Warning: ");
	t.reset().unwrap();
	println!("{}", msg);
	println!("{}: {}", row, line);
	t.fg(term::color::BRIGHT_YELLOW).unwrap();
	println!("{}^{}\n",
		::std::iter::repeat(' ').take(col + (row as f32).log10() as usize + 3)
			.collect::<String>(),
		::std::iter::repeat('~')
			.take(::std::cmp::min(
				pos.end.unwrap_or(pos.start + 1) - pos.start - 1,
				line_len - col))
			.collect::<String>()
	);
	t.reset().unwrap();
}
