// TODO: Compiler plugins.
//       Fucntions marked with a specific attribute are compiled before the rest of the program,
//       and can be executed in a step right after parsing. The functions take the current
//       compiler state as an argument, and can manipulate the AST as well as attributes and such

use std::cmp::min;
use std::fmt::{self, Debug, Display};
use std::iter::{once, repeat};
use std::process;
use std::path::Path;
use std::collections::BTreeSet;
use std::io::{self, Write};
use term::{self, color, Terminal, TerminfoTerminal};
use itertools::Itertools;

pub mod dependency_graph;
pub mod lex;
pub mod ast;
pub mod parse;
pub mod inference;
pub mod monomorphization;
pub mod substitution;

/// A generator of unique type variables
pub struct TypeVarGen(u64);

impl TypeVarGen {
    pub fn new(n: u64) -> Self {
        TypeVarGen(n)
    }

    /// Generates a new, unique type variable
    pub fn gen<'src>(&mut self) -> u64 {
        let n = self.0;
        self.0 += 1;
        n
    }

    pub fn gen_tv<'src>(&mut self) -> ast::Type<'src> {
        ast::Type::Var(ast::TVar {
            id: self.gen(),
            constrs: BTreeSet::new(),
            explicit: None,
        })
    }
}

/// Exit compilation
pub fn exit() -> ! {
    println!("\nError occured during compilation. Exiting");
    process::exit(0)
}

/// Print an error and exit the compilation
pub fn error_exit<E: Display>(msg: E) -> ! {
    let mut t = term::stdout().expect("Could not acquire access to stdout");

    t.fg(color::BRIGHT_RED).ok();
    print!("Error: ");
    t.reset().ok();
    println!("{}", msg);

    exit()
}

/// A position or interval in a string of source code
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SrcPos<'src> {
    filename: &'src Path,
    src: &'src str,
    start: usize,
    end: Option<usize>,
}
impl<'src> SrcPos<'src> {
    /// Construct a new `SrcPos` representing a position in `src`
    fn new_pos(filename: &'src Path, src: &'src str, pos: usize) -> Self {
        SrcPos {
            filename: filename,
            src: src,
            start: pos,
            end: None,
        }
    }

    /// Construct a new `SrcPos` representing an interval in `src`
    fn new_interval(filename: &'src Path, src: &'src str, start: usize, end: usize) -> Self {
        SrcPos {
            filename: filename,
            src: src,
            start: start,
            end: Some(end),
        }
    }

    fn new_dummy() -> Self {
        SrcPos {
            filename: Path::new("DUMMY"),
            src: "DUMMY",
            start: 0,
            end: None,
        }
    }

    fn to(&self, other: &Self) -> Self {
        assert_eq!(
            self.filename, other.filename,
            "ICE: Trying to construct position interval between positions in different files"
        );
        SrcPos {
            filename: self.filename,
            src: self.src,
            start: self.start,
            end: Some(other.end.unwrap_or(other.start)),
        }
    }

    /// [0 .. 10].after([0 .. 3]) = [4 .. 10]
    /// [0 .. 10].after([2 .. 4]) = [5 .. 10]
    fn after(&self, child: &Self) -> Self {
        assert_eq!(
            self.filename, child.filename,
            "ICE: In `after`, child and parent SrcPos are in different files"
        );
        let p_start = self.start;
        let p_end = self.end.expect("ICE: Parent srcpos in `after` is not an interval");
        let c_start = child.start;
        let c_end = child.end.unwrap_or(c_start);
        assert!(c_start >= p_start && c_end <= p_end, "ICE: Child srcpos in `after` is not an element/subset of parent");
        SrcPos {
            filename: self.filename,
            src: self.src,
            start: c_end,
            end: Some(p_end)
        }
    }

    /// Note: for compatibility with tooling, columns are 1-indexed on print
    fn line_len_row_col(&self) -> (&'src str, usize, usize, usize) {
        let mut line_start = 0;

        for (row, line) in self.src.lines().enumerate().map(|(n, line)| (n + 1, line)) {
            let line_len = line.len() + 1; // Include length of newline char

            if line_start <= self.start && self.start < line_start + line_len {
                let col = self.start - line_start;

                return (line, line_len, row, col + 1);
            }
            line_start += line_len;
        }
        unreachable!(
            "Internal compiler error: line_len_row_col: Pos {:?} not reached. src.len(): \
             {}",
            self,
            self.src.len()
        )
    }

    /// Prints a message along with a marked section of the source where the error occured
    ///
    /// # Examples
    /// ```ignore
    /// pos.message("Unexpected string", "Error", color::BRIGHT_RED)
    /// ```
    ///
    /// The preceeding expression might, for a certain `pos` produce the following output
    ///
    /// ```text
    /// 84:4: Error: Unexpected string
    /// 84: let "foo" = 3
    ///         ^~~~
    /// ```
    fn write_message<E: Display, W: Write>(&self, w: &mut W, msg: E, kind: &str, color: color::Color) {
        let (line, line_len, row, col) = self.line_len_row_col();
        let mut t =
            TerminfoTerminal::new(w).expect("Failed to create terminfo terminal of writer `w`");

        t.fg(color).ok();
        write!(t, "{}: ", kind).ok();
        t.reset().ok();
        let nl_align = once('\n')
            .chain(repeat(' ').take(kind.len() + 2))
            .collect::<String>();
        let aligned_msg = msg.to_string()
            .lines()
            .intersperse(&nl_align)
            .collect::<String>();
        writeln!(t, "{}", aligned_msg).ok();
        writeln!(t, "  --> {}:{}:{}", self.filename.display(), row, col).ok();
        writeln!(t, "{}: {}", row, line).ok();
        t.fg(color).ok();
        writeln!(
            t,
            "{}^{}",
            repeat(' ')
                .take(col + (row as f32).log10() as usize + 2)
                .collect::<String>(),
            repeat('^')
                .take(min(
                    self.end.unwrap_or(self.start + 1) - self.start - 1,
                    line_len - col,
                ))
                .collect::<String>()
        ).ok();
        t.reset().ok();
    }

    /// Prints an error message along with a marked section of the source where the error occured
    ///
    /// # Examples
    /// ```ignore
    /// pos.multi_error("Unexpected string")
    /// ```
    ///
    /// The preceeding expression might, for a certain `pos` produce the following output
    ///
    /// ```text
    /// 84:4: Error: Unexpected string
    /// 84: let "foo" = 3
    ///         ^~~~
    /// ```
    pub fn write_error<E: Display, W: io::Write>(&self, w: &mut W, msg: E) {
        self.write_message(w, msg, "Error", color::BRIGHT_RED);
    }

    pub fn print_error<E: Display>(&self, msg: E) {
        self.write_error(&mut io::stdout(), msg)
    }

    /// Like `SrcPos::error`, but exits after message has been printed
    pub fn error_exit<E: Display>(&self, msg: E) -> ! {
        self.print_error(msg);
        exit()
    }

    /// Like `SrcPos::error`, but text is yellow and kind is "Warning"
    pub fn write_warn<S: Display, W: Write>(&self, w: &mut W, msg: S) {
        self.write_message(w, msg, "Warning", color::BRIGHT_YELLOW);
    }

    pub fn print_warn<S: Display>(&self, msg: S) {
        self.write_warn(&mut io::stdout(), msg);
    }

    /// Like `SrcPos::error`, but text is green and kind is "Note"
    pub fn write_note<S: Display, W: Write>(&self, w: &mut W, msg: S) {
        self.write_message(w, msg, "Note", color::BRIGHT_GREEN);
    }

    pub fn print_note<S: Display>(&self, msg: S) {
        self.write_note(&mut io::stdout(), msg);
    }

    /// Like `SrcPos::error`, but text is cyan and kind is "Help"
    pub fn write_help<S: Display, W: Write>(&self, w: &mut W, msg: S) {
        self.write_message(w, msg, "Help", color::BRIGHT_CYAN);
    }

    pub fn print_help<S: Display>(&self, msg: S) {
        self.write_help(&mut io::stdout(), msg);
    }
}
impl<'src> Debug for SrcPos<'src> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.end {
            Some(end) => write!(fmt, "SrcPos {{ start: {}, end: {} }}", self.start, end),
            None => write!(fmt, "SrcPos {{ start: {} }}", self.start),
        }
    }
}
