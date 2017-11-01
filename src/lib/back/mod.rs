use self::llvm::{Context, Builder, Module};
use self::codegen::*;
use {Emission, FileName};
use lib::front::ast;
use std::fs;
use std::io::Write;
use std::process::Command;
use std::env::current_dir;

mod llvm;
mod codegen;

pub fn compile(
    ast: &ast::Module,
    out_file_name: FileName,
    emission: Emission,
    link_libs: &[String],
    lib_paths: &[String],
) {
    let context = Context::new();
    let builder = Builder::new(&context);
    let module = Module::new("main", &context);
    let mut codegenerator = CodeGenerator::new(&context, &builder, &module);

    codegenerator.gen_executable(&ast);

    codegenerator.module.verify().unwrap_or_else(|e| {
        panic!("Verifying module failed\n{}", e)
    });

    match emission {
        Emission::LlvmAsm => {
            let mut ir_file =
                fs::File::create(out_file_name.clone().unwrap_or_with_ext("ll"))
                    .unwrap_or_else(|e| panic!("Failed to open file `{}`, {}", out_file_name, e));

            write!(ir_file, "{:?}", codegenerator.module).unwrap_or_else(|e| {
                panic!("Failed to write IR to `{}`, {}", out_file_name, e)
            })
        }
        Emission::LlvmBc => {
            codegenerator
                .module
                .write_bitcode(&out_file_name
                    .clone()
                    .unwrap_or_with_ext("bc")
                    .to_string_lossy())
                .unwrap_or_else(|e| {
                    panic!("Failed to write bitcode to `{}`, {}", out_file_name, e)
                })
        }
        Emission::Obj => {
            codegenerator
                .module
                .compile(&out_file_name.clone().unwrap_or_with_ext("o"), 0)
                .expect("Failed to compile module")
                .wait()
                .expect("Failed to wait on compilation child");
        }
        Emission::Exe => {
            let obj_path = out_file_name.path().with_extension("o");

            codegenerator
                .module
                .compile(&obj_path, 0)
                .expect("Failed to compile module")
                .wait()
                .expect("Failed to wait on compilation child");

            let mut clang = Command::new("clang");
            clang.arg(&obj_path).args(
                &[
                    "-o",
                    &out_file_name.path().to_string_lossy(),
                ],
            );
            // Add current dir to link dir paths by default
            clang.args(
                &[
                    "-L",
                    current_dir()
                        .expect("Invalid current working directory")
                        .to_str()
                        .expect("Path to current dir is not valid unicode"),
                ],
            );
            for path in lib_paths {
                clang.args(&["-L", path]);
            }
            for lib in link_libs {
                clang.args(&["-l", lib]);
            }

            let output = clang.output().unwrap_or_else(|e| {
                panic!("Failed to execute linking process: `{:?}`\n{}", clang, e)
            });
            fs::remove_file(obj_path).expect("Failed to remove intermediate obj file");
            if !output.status.success() {
                panic!(
                    "Error during linking using clang\n`{:?}`\n{}\nclang exited with: {}",
                    clang,
                    String::from_utf8_lossy(&output.stderr),
                    output.status.code().unwrap_or(0)
                );
            }
        }
    }
}
