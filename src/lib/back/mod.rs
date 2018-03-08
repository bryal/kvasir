use self::llvm::{Context, Builder, Module};
use self::codegen::*;
use Emission;
use lib::CanonPathBuf;
use lib::front::ast;
use std::fs;
use std::io::Write;
use std::process::Command;
use std::env::current_dir;

mod llvm;
mod codegen;

pub fn compile(
    ast: &ast::Ast,
    out_filename: CanonPathBuf,
    explicit_filename: bool,
    emission: Emission,
    link_libs: &[String],
    lib_paths: &[String],
) {
    let context = Context::new();
    let builder = Builder::new(&context);
    let module = Module::new("main", &context);
    let mut codegenerator = CodeGenerator::new(&context, &builder, &module, ast.adts.clone());

    codegenerator.gen_executable(&ast);

    codegenerator.module.verify().unwrap_or_else(|e| {
        panic!(
            "Verifying module failed\nmodule: {:?}\nerror: {}",
            codegenerator.module,
            e
        )
    });

    let with_ext_unless_explicit = |ext| if explicit_filename {
        out_filename.clone()
    } else {
        out_filename.with_extension(ext)
    };

    match emission {
        Emission::LlvmAsm => {
            let ll_filename = with_ext_unless_explicit("ll");
            let mut ir_file = fs::File::create(ll_filename.path()).unwrap_or_else(|e| {
                panic!(
                    "Failed to open file `{}`, {}",
                    out_filename.path().display(),
                    e
                )
            });

            write!(ir_file, "{:?}", codegenerator.module).unwrap_or_else(|e| {
                panic!(
                    "Failed to write IR to `{}`, {}",
                    ll_filename.path().display(),
                    e
                )
            })
        }
        Emission::LlvmBc => {
            let bc_filename = with_ext_unless_explicit("bc");
            codegenerator
                .module
                .write_bitcode(&bc_filename.path().to_string_lossy())
                .unwrap_or_else(|e| {
                    panic!(
                        "Failed to write bitcode to `{}`, {}",
                        bc_filename.path().display(),
                        e
                    )
                })
        }
        Emission::Obj => {
            let obj_filename = with_ext_unless_explicit("o");
            codegenerator
                .module
                .compile(obj_filename.path(), 0)
                .expect("Failed to compile module")
                .wait()
                .expect("Failed to wait on compilation child");
        }
        Emission::Exe => {
            let obj_path = out_filename.path().with_extension("o");

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
                    &out_filename.path().to_string_lossy(),
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
