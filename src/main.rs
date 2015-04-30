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
//! (define C_FOO 1_000: U16) ; == const C_FOO = 1_000_u16;
//! 
//! ; Define a constant C_BAR of type U64, with value 337 of type num::BigInt coerced to U64.
//! ; Number types can only be coerced upwards, to higher precision
//! (define: U64 C_BAR 337: num::BigInt) ; == const C_BAR: u64 = 337_u32;
//! 
//! ; Define a constant C_BAZ of inferred type num::BigInt
//! (define C_BAZ (+ C_FOO C_BAR))
//! 
//! ; Define a function of inferred type. Only specify type of argument `a`, and infer the rest
//! (define (f_foo a: U32) a) ; == fn f_foo(a: u32) -> u32 { a }
//! 
//! ; Try to define a function of inferred type. Don't specify any types. Won't work.
//! (define (f_bar a) a) ; == fn f_foo(a: _) -> _ { a }
//! 
//! ; Define a function of type Fn<(F32), F64>.
//! ; Infer argument type and return value coersion type from function type
//! (define (f_baz: Fn<(F32) F64> a) a) ; == fn tmp(a: _) -> _ {a}; const f_foo: fn(f32) -> f64 = tmp;
//! 
//! The `main` function entry, same as Rust `fn main() { ...`
//! (define (main) (block
//! 	(println! "c_foo: {}, c_bar: {}, c_baz: {}" C_FOO C_BAR C_BAZ)
//! 	(println! "f_foo: {}" (f_baz (as C_BAZ F32)))))
//! ```

#![feature(non_ascii_idents)]

use std::env;
use std::io::Read;
use std::fs;

mod ast;
mod lex;

fn main() {
	let file_name = env::args().skip(1).next().unwrap();

	let mut scr_code = String::with_capacity(4_000);
	fs::File::open(file_name).unwrap().read_to_string(&mut scr_code).unwrap();

	let tokens = lex::tokenize_string(&scr_code).unwrap();
	println!("{:?}\n", tokens);

	println!("{:?}", ast::AST::parse(&tokens).unwrap());
}