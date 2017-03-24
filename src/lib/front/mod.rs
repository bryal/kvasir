// TODO: Compiler plugins.
//       Fucntions marked with a specific attribute are compiled before the rest of the program,
//       and can be executed in a step right after parsing. The functions take the current
//       compiler state as an argument, and can manipulate the AST as well as attributes and such

use std::cmp::min;
use std::fmt::{self, Display, Debug};
use std::iter::repeat;
use std::process;
use term::{self, color};

pub mod lex;
pub mod ast;
pub mod parse;
pub mod inference;

/// Exit compilation
fn exit() -> ! {
    println!("\nError occured during compilation. Exiting\n");
    process::exit(0)
}

/// A position or interval in a string of source code
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct SrcPos<'src> {
    src: &'src str,
    start: usize,
    end: Option<usize>,
    in_expansion: Option<Box<SrcPos<'src>>>,
}
impl<'src> SrcPos<'src> {
    /// Construct a new `SrcPos` representing a position in `src`
    fn new_pos(src: &'src str, pos: usize) -> Self {
        SrcPos {
            src: src,
            start: pos,
            end: None,
            in_expansion: None,
        }
    }
    /// Construct a new `SrcPos` representing an interval in `src`
    fn new_interval(src: &'src str, start: usize, end: usize) -> Self {
        SrcPos {
            src: src,
            start: start,
            end: Some(end),
            in_expansion: None,
        }
    }

    fn line_len_row_col(&self) -> (&'src str, usize, usize, usize) {
        let mut line_start = 0;

        for (row, line) in self.src.lines().enumerate().map(|(n, line)| (n + 1, line)) {
            let line_len = line.len() + 1; // Include length of newline char

            if line_start <= self.start && self.start < line_start + line_len {
                let col = self.start - line_start;

                return (line, line_len, row, col);
            }
            line_start += line_len;
        }
        unreachable!("Internal compiler error: line_len_row_col: Pos {:?} not reached. src.len(): \
                      {}",
                     self,
                     self.src.len())
    }

    fn print_expansion(&self, t: &mut term::StdoutTerminal) {
        if let Some(ref exp) = self.in_expansion {
            exp.print_expansion(t);
        }

        let (line, line_len, row, col) = self.line_len_row_col();

        print!("{}:{}: ", row, col);

        t.fg(color::BRIGHT_MAGENTA).ok();
        println!("In expansion");
        t.reset().ok();

        println!("{}: {}", row, line);

        t.fg(color::BRIGHT_MAGENTA).ok();
        println!("{}^{}",
                 repeat(' ')
                     .take(col + (row as f32).log10() as usize + 3)
                     .collect::<String>(),
                 repeat('~')
                     .take(min(self.end.unwrap_or(self.start + 1) - self.start - 1,
                               line_len - col))
                     .collect::<String>());
        t.reset().ok();
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
    fn message<E: Display>(&self, msg: E, kind: &str, color: color::Color) {
        let (line, line_len, row, col) = self.line_len_row_col();
        let mut t = term::stdout().expect("Could not acquire access to stdout");

        if let Some(ref exp) = self.in_expansion {
            exp.print_expansion(&mut *t);
        }

        print!("{}:{}: ", row, col);

        t.fg(color).ok();
        print!("{}: ", kind);
        t.reset().ok();

        println!("{}", msg);
        println!("{}: {}", row, line);

        t.fg(color).ok();
        println!("{}^{}",
                 repeat(' ')
                     .take(col + (row as f32).log10() as usize + 3)
                     .collect::<String>(),
                 repeat('~')
                     .take(min(self.end.unwrap_or(self.start + 1) - self.start - 1,
                               line_len - col))
                     .collect::<String>());
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
    pub fn error<E: Display>(&self, msg: E) {
        self.message(msg, "Error", color::BRIGHT_RED);
    }

    /// Like `SrcPos::error`, but exits after message has been printed
    pub fn error_exit<E: Display>(&self, msg: E) -> ! {
        self.error(msg);

        exit()
    }

    /// Like `SrcPos::error`, but text is yellow and kind is "Warning"
    pub fn warn<S: Display>(&self, msg: S) {
        self.message(msg, "Warning", color::BRIGHT_YELLOW);
    }

    /// Like `SrcPos::error`, but text is green and kind is "Note"
    pub fn note<S: Display>(&self, msg: S) {
        self.message(msg, "Note", color::BRIGHT_GREEN);
    }

    /// Like `SrcPos::error`, but text is cyan and kind is "Help"
    pub fn help<S: Display>(&self, msg: S) {
        self.message(msg, "Help", color::BRIGHT_CYAN);
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

pub fn error<E: Display>(e: E) -> ! {
    let mut t = term::stdout().expect("Could not acquire access to stdout");

    t.fg(color::BRIGHT_RED).ok();
    print!("Error: ");
    t.reset().ok();

    println!("{}", e);

    println!("\nError occured during compilation. Exiting\n");
    exit()
}
