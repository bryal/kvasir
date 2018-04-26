//! # The Kvasir Programming Language
//!
//! ## Envisioned syntax
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
//! ; add : Num → Num → Num
//! ; ⇒ α : Num, β : Num in add α β ⇒ λ1.λβ.add 1 β : Num → Num → Num
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
// TODO: Allocation should be handled through third-party function, like jemalloc, libc malloc
// TODO: Specify allocator with cfg flag. This allows for linking with libs
//       using different allocators
// TODO: Slice representation? Pointer to len and data is probably easiest.
//       Slice of `T`s with len N: `| len: usize | data: N * sizeof(T) |`
// TODO: `extern` declarations for linking in C functions
// TODO: Interface for AST through which multiple lexer/parsers can be implemented
//       for the language.
//       Similar to how racker supports multiple source languages
//       Also serves as a way to save keywords and such, e.g. core types, as associated constants
// TODO: Warn if a macro producing an expression is called using brackers, [], and vice versa
// TODO: Tests. Maybe QuickCheck?
// TODO: Add hooks for viewing of AST for 3rd party tools to use
// TODO: linters. E.g linter that searches libraries for functions that do what
//       a user expression does.
//       Lint for unnecessarily specific types in function signatures
// TODO: Implement some of current warnings, and maybe errors, as lints.
// TODO: Optionally enabled used of `Coerce` trait to allow implicit coercion between
//       'coerceable' type pairs. E.g. `Int32` to `UInt8`, or `
// TODO: Add frontends for existing laanguages to easily port projects
// TODO: Prioritize more specialized implementations of traits over more general implementations.
//       E.g. `(impl Drop (Vec String))` comes before
//            `(let-type T (impl Drop (Vec T)))` which comes before
//            `(let-type [T Iter Extend Clone] (impl Drop T))` which comes before
//            `(let-type T (impl Drop for T any T))`
// TODO: Base macro system on pure functions that has syntax trees as input and output.
//       This would require some kind of interpretation in order to execute code at compile time

#![feature(non_ascii_idents, box_syntax, box_patterns)]

extern crate bitflags;
extern crate cbox;
extern crate getopts;
extern crate itertools;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate llvm_sys;
#[macro_use]
extern crate maplit;
extern crate term;

use getopts::Options;
use lib::CanonPathBuf;
use lib::collections::AddMap;
use lib::back::compile;
use lib::front::inference::infer_types;
use lib::front::parse::parse_program;
use std::{env, fmt, time};

mod lib;

/// Enum of the different output formats of the compiler
pub enum Emission {
    /// Human readable LLVM assembly language code
    LlvmAsm,
    /// LLVM bitcode
    LlvmBc,
    /// Linkable object code
    Obj,
    /// An executable binary
    Exe,
}
impl<S: AsRef<str> + fmt::Display> From<S> for Emission {
    fn from(s: S) -> Emission {
        match s.as_ref() {
            "llvm-ir" => Emission::LlvmAsm,
            "llvm-bc" => Emission::LlvmBc,
            "obj" => Emission::Obj,
            "exe" => Emission::Exe,
            _ => panic!("Unknown emission type `{}`", s),
        }
    }
}

#[cfg(windows)]
const BIN_EXT: &'static str = "exe";
#[cfg(not(windows))]
const BIN_EXT: &'static str = "bin";

fn print_usage(program: &str, opts: Options) {
    let brief = format!("Usage: {} [options] SOURCE-FILE", program);
    print!("{}", opts.usage(&brief));
}

fn main() {
    let start_time = time::Instant::now();
    let args: Vec<_> = env::args().collect();
    let bin_name = args[0].clone();
    let mut opts = Options::new();
    opts.optopt("o", "out-file", "Write output to <FILENAME>", "FILENAME")
        .optopt(
            "",
            "emit",
            "Specify the type of output for the compiler to emit",
            "llvm-ir|llvm-bc|obj|exe",
        )
        .optmulti("l", "", "Link with <LIBRARY>", "LIBRARY")
        .optmulti("L", "", "Add <PATH> to the library search path", "PATH")
        .optflag("h", "help", "Display this help menu");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => panic!(e),
    };
    if matches.opt_present("h") {
        print_usage(&bin_name, opts);
        return;
    }
    let inp_filename = if !matches.free.is_empty() {
        CanonPathBuf::new(&matches.free[0]).expect("Failed to canonicalize input filename")
    } else {
        print_usage(&bin_name, opts);
        return;
    };
    let out_filename = matches
        .opt_str("o")
        .map(|p| CanonPathBuf::new(&p).expect("Failed to canonicalize output filename"))
        .unwrap_or(inp_filename.with_extension(BIN_EXT));
    {
        let inp_file_dir = inp_filename
            .path()
            .parent()
            .expect("Failed to get parent dir of input file");
        env::set_current_dir(inp_file_dir).expect("Failed to change dir to dir of input file")
    }

    let explicit_out_filename = matches.opt_str("o").is_some();
    let emission = matches
        .opt_str("emit")
        .map(|s| s.into())
        .unwrap_or(Emission::Exe);
    let link_libs = matches.opt_strs("l");
    let lib_paths = matches.opt_strs("L");

    println!("    Compiling {}", inp_filename.path().display());

    let mut type_var_generator = lib::front::TypeVarGen::new(0);
    let sources = AddMap::new();
    let mut ast = parse_program(inp_filename, &sources, &mut type_var_generator);

    infer_types(&mut ast, &mut type_var_generator);
    //println!("inferred:\n\n{}", ast);
    compile(
        &ast,
        out_filename,
        explicit_out_filename,
        emission,
        &link_libs,
        &lib_paths,
    );

    println!(
        "    Finished building target in {} secs",
        start_time.elapsed().as_secs()
    )
}
