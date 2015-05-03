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

//! Rust and Scheme inspired implementation of LISP
//!
//! # Envisioned syntax
//! ```ignore
//! (extern crate num)
//!
//! ; Types are static and can be specified with `: <TYPE>` or inferred, like in Rust.
//!
//! ; `define` translates to `const` and `fn` in Rust.
//!
//! ; Define a constant C_FOO with value 1_000 of type U32
//! {define C_FOO 1_000: U16} ; == const C_FOO = 1_000_u16;
//!
//! ; Define a constant C_BAR of type U64, with value 337 of type num::BigInt coerced to U64.
//! ; Number types can only be coerced upwards, to higher precision
//! {define: U64 C_BAR 337: num::BigInt} ; == const C_BAR: u64 = 337_u32;
//!
//! ; Define a constant C_BAZ of inferred type num::BigInt
//! {define C_BAZ (+ C_FOO C_BAR)}
//!
//! ; Define a function of inferred type. Only specify type of argument `a`, and infer the rest
//! {define (f_foo a: U32) a} ; == fn f_foo(a: u32) -> u32 { a }
//!
//! ; Try to define a function of inferred type. Don't specify any types. Won't work.
//! {define (f_bar a) a} ; == fn f_foo(a: _) -> _ { a }
//!
//! ; Define a function of type Fn<(F32), F64>.
//! ; Infer argument type and return value coersion type from function type
//! {define (f_baz: Fn<(F32) F64> a) a} ; == fn tmp(a: _) -> _ {a}; const f_foo: fn(f32) -> f64 = tmp;
//!
//! The `main` function entry, same as Rust `fn main() { ...`
//! {define (main) (block
//! 	(println! "c_foo: {}, c_bar: {}, c_baz: {}" C_FOO C_BAR C_BAZ)
//! 	(println! "f_foo: {}" (f_baz (as C_BAZ F32))))}
//! ```

// TODO: Compile time execution. By marking functions as pure,
// enable calculation of constants from these functions at compile time.

// TODO: Higher Kinded Types. Like Functor which would provide map for a generic container

// TODO: Find errors in code. When lexing, produce a map of token indices =>
// line and col in source. When parsing, pass along token index.

#![feature(non_ascii_idents, box_patterns, rustc_private)]

extern crate getopts;
#[macro_use]
extern crate bitflags;

use getopts::Options;
use std::env;
use std::io::{ Read };
use std::fs::File;
use std::path::PathBuf;

use compile::compile;

mod compile;
mod ast;
mod lex;

#[cfg(unix)]
const BIN_EXTENSION: &'static str = "bin";
#[cfg(windows)]
const BIN_EXTENSION: &'static str = "exe";

bitflags! {
	flags Emit: u16 {
		const EMIT_RUST = 1,
	}
}

fn print_usage(program: &str, opts: Options) {
	let brief = format!("Usage: {} [options] SOURCE-FILE", program);
	print!("{}", opts.usage(&brief));
}

fn main() {
	let args: Vec<_> = env::args().collect();
	let bin_name = args[0].clone();

	let mut opts = Options::new();
	opts.optopt("o", "out-file", "Set output file name", "NAME");
	opts.optopt("", "sysroot", "Specify sysroot for when looking for rust libs, \
		e.g. /usr/local/ or C:/Program Files/Rust/. \
		Do this when rustc complains about missing crates", "DIR");
	opts.optflag("", "emit-rust", "Emit transpiled rust code");
	opts.optflag("h", "help", "Print this help menu");

	let matches = match opts.parse(&args[1..]) {
		Ok(m) => m,
		Err(e) => panic!(e)
	};

	if matches.opt_present("h") {
		print_usage(&bin_name, opts);
		return;
	}

	let inp_file_name = if !matches.free.is_empty() {
		PathBuf::from(matches.free[0].clone())
	} else {
		print_usage(&bin_name, opts);
		return;
	};

	let out_file_name = match matches.opt_str("o") {
		Some(o) => PathBuf::from(o),
		None => {
			let mut o = inp_file_name.clone();
			o.set_extension(BIN_EXTENSION);
			o
		}
	};
	let sysroot = matches.opt_str("sysroot").map(|s| PathBuf::from(s));

	let mut emissions = Emit::empty();
	for emission in [(EMIT_RUST, matches.opt_present("emit-rust"))].iter()
		.filter_map(|&(e, b)| if b { Some(e) } else { None })
	{
		emissions.insert(emission);
	}

	let mut scr_code = String::with_capacity(4_000);
	File::open(inp_file_name).unwrap().read_to_string(&mut scr_code).unwrap();

	let tokens = lex::tokenize_string(&scr_code).unwrap();

	let mut ast = ast::AST::parse(&tokens).unwrap();
	ast.infer_types();

	compile(&ast, out_file_name, sysroot, emissions);
}
