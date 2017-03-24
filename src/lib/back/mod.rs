
use {Emission, FileName};
use lib::front::ast;
use llvm::{Context, Builder, Module};
use self::llvm::*;
use std::fs;
use std::io::Write;
use std::process::Command;

mod llvm;

pub fn compile(ast: &ast::Module,
               out_file_name: FileName,
               emission: Emission,
               link_libs: &[String],
               lib_paths: &[String]) {
    let context = Context::new();
    let builder = Builder::new(&context);
    let module = Module::new("main", &context);
    let codegenerator = CodeGenerator::new(&context, &builder, &module);

    let mut env = Env::new();

    codegenerator.gen_extern_decls(&mut env, &ast.extern_funcs);

    codegenerator.gen_static_defs(&mut env, &ast.static_defs);

    //    println!("module: {:?}", codegenerator.module);

    codegenerator.module.verify().unwrap_or_else(|e| panic!("Verifying module failed\n{}", e));

    match emission {
        Emission::LlvmAsm => {
            let mut ir_file = fs::File::create(out_file_name.clone().unwrap_or_with_ext("ll"))
                .unwrap_or_else(|e| panic!("Failed to open file `{}`, {}", out_file_name, e));

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
