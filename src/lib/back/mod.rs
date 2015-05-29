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

//! For info about compilation of rust source, check out rustc_driver doc

extern crate rustc_trans;
extern crate rustc_driver;

use std::path::PathBuf;
use std::io::Write;
use std::fs::File;

use self::rustc_trans::session::config::{ build_session_options, build_configuration, OutputType, Input };
use self::rustc_trans::session::{ build_session, Session };
use self::rustc_driver::{ driver, RustcDefaultCalls, CompilerCalls, handle_options };
use self::emit::generate_rust_src;
use lib::AST;
use { Emit, EMIT_RUST };

pub mod emit;

#[cfg(unix)]
const SYSROOT: &'static str = "/usr/local/";
#[cfg(windows)]
const SYSROOT: &'static str = "C:/Program Files/Rust nightly/";

/// Build a basic session object to output a compiled binary.
fn basic_session(sysroot: PathBuf) -> Session {
	// TODO: Add support for custom flags to here, like unstability and optimization
	let matches = handle_options(vec!["rustc".into(), "-".into()]).unwrap();
	let mut opts = build_session_options(&matches);

	opts.output_types = vec![OutputType::OutputTypeExe];
	opts.maybe_sysroot = Some(sysroot);

	build_session(opts, None, rustc_driver::diagnostics_registry())
}

pub fn compile(ast: &AST, out_file: PathBuf, sysroot: Option<PathBuf>, emission: Emit) {
	let rust_src = generate_rust_src(ast);

	if emission.contains(EMIT_RUST) {
		let mut f = out_file.clone();
		f.set_extension("rs");
		File::create(f).unwrap().write_all(rust_src.as_bytes()).unwrap();
	}

	let input = Input::Str(rust_src);

	let session = basic_session(match sysroot {
		Some(path) => path,
		None => PathBuf::from(SYSROOT)
	});
	let cfg = build_configuration(&session);

	let mut callbacks = RustcDefaultCalls;
	let control = callbacks.build_controller(&session);
	driver::compile_input(session, cfg, &input, &None, &Some(out_file), None, control)
}
