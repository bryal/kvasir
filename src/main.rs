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
//! # Envisioned syntax⊢
//! ```scheme
//! ; Types are static and can be annotated with `(:TYPE EXPR)` or inferred, similar to Rust.
//!
//! ; Define a constant C_FOO with value 1_000 of type U32
//! > (def-const C_FOO (:U16 1_000))
//! C_FOO :: U16
//!
//! ; Define a constant C_BAR of type U64, with value of C_FOO of type U16 coerced to U64.
//! ; Number types can only be coerced upwards, to higher precision
//! > (def-const C_BAR (:U64 C_FOO))
//! C_BAR :: U64
//!
//! ; Define a constant C_BAZ of inferred type U64. The result from adding numbers with different
//! ; precision gets the type of the highest precision type of the two
//! > (def-const C_BAZ (+ C_FOO C_BAR))
//! C_BAZ :: U64
//!
//! ; Define a function of inferred polymorphic type.
//! > (def-func (f_foo a) a)
//! ; which is equivalent to
//! > (def-const f_foo (λ (a) a))
//! f_foo :: ∀__Polya . __Polya → __Polya
//!
//! ; Define a function of inferred constrained type.
//! ; add : Num → Num → Num ⇒ α : Num, β : Num in add α β ⇒ λ1.λβ.add 1 β : Num → Num → Num
//! > (def-func (inc n) (+ 1 n))
//! inc :: Num → Num
//!
//! The `main` function entry, same as Rust `fn main() { ...`
//! (def-func (main) (block
//! 	(println! "c_foo: {}, c_bar: {}, c_baz: {}" C_FOO C_BAR C_BAZ)
//! 	(println! "f_foo: {}" (f_baz (as C_BAZ F32)))))
//! ```

// TODO: Compile time execution. By marking functions as pure,
//       enable calculation of constants from these functions at compile time.
// TODO: Higher Kinded Types. Like Functor which would provide map for a generic container
// TODO: Formally prove that all type inference is correct using
//       [Damas-Hindley-Miller](http://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system).
//       [Good explanation](http://stackoverflow.com/questions/12532552/what-part-of-milner-hindley-do-you-not-understand)
// TODO: Make symbols interned. Maybe at compile time, build a table of all symbols and substitute
//       uses in code with references to this table.
//       When comparing for equality, just test for reference equality
// TODO: Simple creation of heterogenous list by supplying a sum type that implements From for
//       all different elements. For `quote` it would be something like:
//           (enum Syntax (Symbol Symbol) (List (List Syntax)) (Number Number) (String String))
//           (impl From (Symbol) for Syntax ((define (from s) (Syntax\Symbol s))))
//           ...
//           (list of Syntax "foo" 'bar 42))
//       =>
//           (list (Syntax\String "foo") (Syntax\Symbol 'bar) (Syntax\Number 42))

#![feature(non_ascii_idents, box_patterns, map_in_place, drain, split_off, slice_extras, fs_canonicalize)]

#[macro_use]
extern crate lazy_static;
extern crate getopts;
#[macro_use]
extern crate bitflags;
extern crate term;

use getopts::Options;
use std::env;
use std::io::{ Read };
use std::fs::{ File, canonicalize };
use std::path::PathBuf;

use lib::{ token_trees_from_src, expand_macros };
use lib::front::parse;

mod lib;

#[cfg(not(windows))]
const BIN_EXTENSION: &'static str = "bin";
#[cfg(windows)]
const BIN_EXTENSION: &'static str = "exe";

// bitflags! {
// 	flags Emit: u16 {
// 		const EMIT_RUST = 1,
// 	}
// }

fn print_usage(program: &str, opts: Options) {
	let brief = format!("Usage: {} [options] SOURCE-FILE", program);
	print!("{}", opts.usage(&brief));
}

fn main() {
	let args: Vec<_> = env::args().collect();
	let bin_name = args[0].clone();

	let mut opts = Options::new();
	opts.optopt("o", "out-file", "Set output file name", "NAME");
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

	// let mut emissions = Emit::empty();
	// for emission in [(EMIT_RUST, matches.opt_present("emit-rust"))].iter()
	// 	.filter_map(|&(e, b)| if b { Some(e) } else { None })
	// {
	// 	emissions.insert(emission);
	// }

	println!("    Compiling {}", canonicalize(inp_file_name.as_path()).unwrap().to_string_lossy());

	let mut src_code = String::with_capacity(4_000);
	File::open(inp_file_name).unwrap().read_to_string(&mut src_code).unwrap();

	let token_tree = token_trees_from_src(&src_code);

	// println!("TOKEN TREE{:#?}", token_tree);

	let expanded_macros = expand_macros(&token_tree);

	// println!("MACRO EXPANDED: {:#?}", expanded_macros);

	let mut ast = parse::AST::parse(&expanded_macros);
	// println!("AST PARSED:\n{:#?}\n", ast);

	ast.remove_unused_consts();
	// println!("AST REMOVED UNUSED:\n{:#?}\n", ast);

	ast.infer_types();
	println!("AST INFERED:\n{:#?}\n", ast);
}
