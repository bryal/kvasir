pub use self::collections::ScopeStack;
use std::io;
use std::path::{PathBuf, Path};

#[macro_use]
pub mod front;
pub mod back;
pub mod collections;

/// A path-buffer that is guaranteed to be canonical
#[derive(PartialEq, Clone)]
pub struct CanonPathBuf(PathBuf);

impl CanonPathBuf {
    pub fn new(path: &str) -> io::Result<Self> {
        PathBuf::from(path).canonicalize().map(
            |pb| CanonPathBuf(pb),
        )
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
