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

//! Build a wrapper for some llvm functions that require manual linking

use std::process::{ Command, Output };
use std::env;
use std::fs::File;
use std::path::PathBuf;
use std::io::Write;

fn output_to_string(output: Output) -> String {
	if output.status.success() {
		String::from_utf8_lossy(&output.stdout).into_owned()
	} else {
		panic!("\nstatus: {}\n\nstdout: {}\n\nstderr: {}",
			output.status,
			String::from_utf8_lossy(&output.stdout),
			String::from_utf8_lossy(&output.stderr))
	}
}

// TODO: Consider escaped spaces and spaces in strings
fn split_args(args: &str) -> Vec<&str> {
	args.split_whitespace().collect()
}

fn main() {
	let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

	let mut log = File::create("/home/bryal/Dropbox/Program/Rust/test-rs/llvm_build.log").unwrap();

	let mut c1 = Command::new("clang");

	let cflags = Command::new("llvm-config")
		.arg("--cflags")
		.output()
		.map(output_to_string)
		.unwrap();

	let obj_path = out_dir.join("llvm_wrapper.o");
	c1.args(&["-c", "foreign/llvm_wrapper.c"])
		.arg("-g")
		.args(&split_args(&cflags))
		.arg("-o").arg(&obj_path);

	let mut c2 = Command::new("clang++");

	let link_flags = Command::new("llvm-config")
		.arg("--cxxflags")
		.arg("--ldflags")
		.args(&["--libs", "all"])
		.arg("--system-libs")
		.output()
		.map(output_to_string)
		.unwrap();

	let so_path = out_dir.join("libllvm_wrapper.so");
	c2.arg("-shared")
		.arg(&obj_path)
		.args(&split_args(&link_flags))
		.arg("-lffi")
		.arg("-o").arg(&so_path);

	writeln!(log, "c1: {:?}", c1).ok();
	writeln!(log, "c2: {:?}", c2).ok();

	writeln!(log, "c1 out: {}", output_to_string(c1.output().unwrap())).ok();
	writeln!(log, "c2 out: {}", output_to_string(c2.output().unwrap())).ok();

	writeln!(log, "in OUT_DIR, {}:", out_dir.display());
	for entry in std::fs::read_dir(out_dir.clone()).unwrap() {
		writeln!(log, "{:?}", entry.unwrap().path()).ok();
	}

	println!("cargo:rustc-link-search=native={}", out_dir.display());
	println!("cargo:rustc-link-lib=dylib=llvm_wrapper");
}
