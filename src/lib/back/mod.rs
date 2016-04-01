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

use std::fs;
use std::io::Write;
use std::process::Command;
use llvm::Context;
use lib::front::ast::Module;
use {Emission, FileName};
use self::llvm::*;

mod llvm;

pub fn compile(ast: &Module,
               out_file_name: FileName,
               emission: Emission,
               link_libs: &[String],
               lib_paths: &[String]) {
    let context = Context::new();

    let codegenerator = CodeGenerator::new(&context);

    let mut env = Env::new();

    codegenerator.gen_extern_decls(&mut env, &ast.extern_funcs);

    codegenerator.gen_const_defs(&mut env, &ast.const_defs);

    println!("module: {:?}", codegenerator.module);

    codegenerator.module.verify().unwrap_or_else(|e| panic!("Verifying module failed\n{}", e));

    match emission {
        Emission::LlvmAsm => {
            let mut ir_file = fs::File::create(out_file_name.clone().unwrap_or_with_ext("ll"))
                                  .unwrap_or_else(|e| {
                                      panic!("Failed to open file `{}`, {}", out_file_name, e)
                                  });

            write!(ir_file, "{:?}", codegenerator.module)
                .unwrap_or_else(|e| panic!("Failed to write IR to `{}`, {}", out_file_name, e))
        }
        Emission::LlvmBc => {
            codegenerator.module
                         .write_bitcode(&out_file_name.clone()
                                                      .unwrap_or_with_ext("bc")
                                                      .to_string_lossy())
                         .unwrap_or_else(|e| {
                             panic!("Failed to write bitcode to `{}`, {}", out_file_name, e)
                         })
        }
        Emission::Obj => {
            codegenerator.module
                         .compile(&out_file_name.clone().unwrap_or_with_ext("o"), 0)
                         .unwrap();
        }
        Emission::Bin => {
            let obj_path = out_file_name.path().with_extension("o");

            codegenerator.module
                         .compile(&obj_path, 0)
                         .unwrap();

            let mut clang = Command::new("clang");
            clang.arg(obj_path).args(&["-o", &out_file_name.path().to_string_lossy()]);
            for path in lib_paths {
                clang.args(&["-L", path]);
            }
            for lib in link_libs {
                clang.args(&["-l", lib]);
            }

            let output = clang.output().unwrap_or_else(|e| {
                panic!("Failed to execute linking process: `{:?}`\n{}", clang, e)
            });
            if !output.status.success() {
                panic!("Error during linking using clang\n`{:?}`\n{}\nclang exited with: {}",
                       clang,
                       String::from_utf8_lossy(&output.stderr),
                       output.status.code().unwrap_or(0));
            }
        }
    }
}
