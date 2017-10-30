//! Tom Bebbingtons llvm-rs library as a module. A high-level LLVM wrapper.
//!
//! This library provides wrappers for LLVM that are memory-safe and follow
//! Rust idioms.
//!
//! The original LLVM reference is available [here](http://llvm.org/doxygen/)
//! but take note that this isn't as thorough as this documentation.

#[macro_use]
mod macros;
mod buffer;
mod block;
mod builder;
mod compile;
mod context;
mod engine;
mod module;
mod object;
mod target;
pub mod types;
pub mod value;
mod util;

pub use cbox::{CBox, CSemiBox};
pub use self::builder::Builder;
pub use self::block::BasicBlock;
pub use self::compile::Compile;
pub use self::context::{Context, GetContext};
pub use self::engine::{JitEngine, JitOptions, Interpreter, ExecutionEngine, GenericValue,
                       GenericValueCast};
pub use self::module::{AddressSpace, Module, Functions};
pub use self::object::{ObjectFile, Symbol, Symbols};
pub use self::target::{TargetData, Target};
pub use self::types::*;
pub use self::value::{Alias, Arg, Value, Function, GlobalValue, GlobalVariable, Linkage, Predicate};
pub use self::util::Sub;
