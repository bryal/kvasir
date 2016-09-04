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
// TODO: Allocation should be handled through third-party function, like jemalloc, libc malloc
// TODO: Specify allocator with cfg flag. This allows for linking with libs using different allocators
// TODO: Slice representation? Pointer to len and data is probably easiest.
//       Slice of `T`s with len N: `| len: usize | data: N * sizeof(T) |`
// TODO: `extern` declarations for linking in C functions
// TODO: Interface for AST through which multiple lexer/parsers can be implemented for the language.
//       Similar to how racker supports multiple source languages
//       Also serves as a way to save keywords and such, e.g. core types, as associated constants
// TODO: Make use of different brackets to discriminate between expressions and items/syntax sugar
//       e.g: `(let [[a 3] [b 9]] (+ a b))`
// TODO: Warn if a macro producing an expression is called using brackers, [], and vice versa
// TODO: Tests. Maybe QuickCheck?
// TODO: Add hooks for viewing of AST for 3rd party tools to use
// TODO: linters. E.g linter that searches libraries for functions that do what
//       a user expression does.
//       Lint for unnecessarily specific types in function signatures
// TODO: Implement some of current warnings, and maybe errors, as lints.
// TODO: 3 message categories. error, warning, hint. disabling hints disables lints
// TODO: Optionally enabled used of `Coerce` trait to allow implicit coercion between
//       'coerceable' type pairs. E.g. `Int32` to `UInt8`, or `
// TODO: Add frontends for existing laanguages to easily port projects
// TODO: Prioritize more specialized implementations of traits over more general implementations.
//       E.g. `(impl Drop (Vec String))` comes before
//            `(let-type T (impl Drop (Vec T)))` which comes before
//            `(let-type [T Iter Extend Clone] (impl Drop T))` which comes before
//            `(let-type T (impl Drop for T any T))`

#![feature(non_ascii_idents, box_patterns)]

#![deny(missing_docs)]

#[macro_use]
extern crate lazy_static;
extern crate getopts;
#[macro_use]
extern crate bitflags;
extern crate term;
extern crate llvm;
extern crate llvm_sys;
extern crate itertools;

use std::{env, fmt};
use std::io::Read;
use std::fs::{File, canonicalize};
use std::path::{Path, PathBuf};
use getopts::Options;
use lib::{concrete_syntax_trees_from_src, expand_macros};
use lib::front::parse::parse;
use lib::front::inference::infer_types;
use lib::middle::clean_ast;
use lib::back::compile;

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
    Bin,
}
impl<S: AsRef<str> + fmt::Display> From<S> for Emission {
    fn from(s: S) -> Emission {
        match s.as_ref() {
            "llvm-ir" => Emission::LlvmAsm,
            "llvm-bc" => Emission::LlvmBc,
            "obj" => Emission::Obj,
            _ => panic!("Unknown emission type `{}`", s),
        }
    }
}

/// A filename that is either specified by the user or an inferred default
#[derive(Clone)]
pub enum FileName {
    /// A user-specified filename. Will not be modified
    Some(PathBuf),
    /// A default filename. The extension will change depending on the emission type
    Default(PathBuf),
}
impl FileName {
    /// Get the filename as a `&Path`
    pub fn path(&self) -> &Path {
        match *self {
            FileName::Some(ref p) => p,
            FileName::Default(ref p) => p,
        }
    }

    /// Modifies the filename by applying a function to the contained `PathBuf`.
    pub fn map<F: Fn(PathBuf) -> PathBuf>(self, f: F) -> FileName {
        match self {
            FileName::Some(p) => FileName::Some(f(p)),
            FileName::Default(p) => FileName::Default(f(p)),
        }
    }

    /// If `Some`, unwrap it. If `Default`, change the extension before unwrapping
    pub fn unwrap_or_with_ext(self, ext: &str) -> PathBuf {
        match self {
            FileName::Some(p) => p,
            FileName::Default(p) => p.with_extension(ext),
        }
    }
}
impl fmt::Display for FileName {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.path().display(), fmt)
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
    let args: Vec<_> = env::args().collect();
    let bin_name = args[0].clone();

    let mut opts = Options::new();
    opts.optopt("o", "out-file", "Write output to <FILENAME>", "FILENAME")
        .optopt("",
                "emit",
                "Specify the type of output for the compiler to emit",
                "llvm-ir|llvm-bc|obj")
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

    let inp_file_name = if !matches.free.is_empty() {
        PathBuf::from(matches.free[0].clone())
    } else {
        print_usage(&bin_name, opts);
        return;
    };

    let out_file_name = matches.opt_str("o")
                               .map(|p| FileName::Some(PathBuf::from(p)))
                               .unwrap_or(FileName::Default(inp_file_name.with_extension(BIN_EXT)))
                               .map(|filename| {
                                   let parent = match filename.parent() {
                                       None => "./".as_ref(),
                                       Some(p) if p == Path::new("") => "./".as_ref(),
                                       Some(p) => p,
                                   };
                                   canonicalize(parent)
                                       .expect("Failed to canonicalize output filename")
                                       .join(filename.file_name().expect("No filename supplied"))
                               });

    let emission = matches.opt_str("emit").map(|s| s.into()).unwrap_or(Emission::Bin);

    let link_libs = matches.opt_strs("l");
    let lib_paths = matches.opt_strs("L");

    println!("    Compiling {}",
             canonicalize(inp_file_name.as_path())
                 .expect("Failed to canonicalize input filename")
                 .to_string_lossy());

    let mut src_code = String::with_capacity(4_000);
    let src_file = File::open(&inp_file_name)
                       .expect(&format!("Failed to open file `{}`", inp_file_name.display()))
                       .read_to_string(&mut src_code)
                       .expect(&format!("Reading contents of `{}` failed",
                                        inp_file_name.display()));

    let csts = concrete_syntax_trees_from_src(&src_code);

    // println!("TOKEN TREE{:#?}", token_tree);

    let expanded_macros = expand_macros(&csts);

    // println!("MACRO EXPANDED: {:#?}", expanded_macros);

    let mut ast = parse(&expanded_macros);
    // println!("AST PARSED:\n{:#?}\n", ast);

    clean_ast(&mut ast);
    // println!("AST REMOVED UNUSED:\n{:#?}\n", ast);

    infer_types(&mut ast);
    println!("AST INFERED:\n{:#?}\n", ast);

    compile(&ast, out_file_name, emission, &link_libs, &lib_paths);
}
