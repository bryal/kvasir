pub use self::collections::ScopeStack;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

#[macro_use]
pub mod front;
pub mod back;
pub mod collections;

/// A path-buffer that is guaranteed to be canonical
#[derive(PartialEq, Clone)]
pub struct CanonPathBuf(PathBuf);

impl CanonPathBuf {
    pub fn new(path: &str) -> io::Result<Self> {
        PathBuf::from(path)
            .canonicalize()
            .map(|pb| CanonPathBuf(pb))
    }

    pub fn path(&self) -> &Path {
        self.0.as_ref()
    }

    pub fn with_extension(&self, ext: &str) -> Self {
        CanonPathBuf(self.0.with_extension(ext))
    }
}

impl AsRef<Path> for CanonPathBuf {
    fn as_ref(&self) -> &Path {
        self.path()
    }
}

pub struct ErrCode {
    pub module: &'static str,
    pub number: usize,
}

impl ErrCode {
    pub fn undefined() -> Self {
        ErrCode {
            module: "UNDEFINED",
            number: 0,
        }
    }
}

impl fmt::Display for ErrCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.module, self.number)
    }
}
