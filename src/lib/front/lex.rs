// The MIT License (MIT)
//
// Copyright (c) 2015 Johan Johansson
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::fmt;
use std::borrow::Cow;
use super::SrcPos;
use self::LexErr::*;

enum LexErr {
    UnknownEscape,
    InvalidEscapeSeq,
    UntermStr,
    InvalidStrDelim,
    InvalidNum,
    InvalidIdent,
    UndelimItem,
    Unexpected(&'static str),
}
impl fmt::Display for LexErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            UnknownEscape => write!(f, "Unknown character escape"),
            InvalidEscapeSeq => write!(f, "Invalid escape sequence"),
            UntermStr => write!(f, "Unterminated string literal"),
            InvalidStrDelim => write!(f, "Invalid string literal delimiter"),
            InvalidNum => write!(f, "Invalid numeric literal"),
            InvalidIdent => write!(f, "Invalid ident"),
            UndelimItem => write!(f, "Undelimited item"),
            Unexpected(s) => write!(f, "Unexpected {}", s),
        }
    }
}

fn unescape_char(c: char) -> Option<char> {
    // TODO: add more escapes
    match c {
        'n' => Some('\n'),
        't' => Some('\t'),
        '0' => Some('\0'),
        _ => None,
    }
}

/// A token
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token<'src> {
    LParen,
    RParen,
    Ident(&'src str),
    Num(&'src str),
    Str(Cow<'src, str>),
    Quote,
}

/// Tokenize the string literal in `src` at `start`.
/// Return the unescaped literal as a `Token` and it's length,
/// including delimiting characters, in the source.
fn tokenize_str_lit(src: &str, start: usize) -> (Token, usize) {
    let mut s = String::new();

    let mut chars = src[start + 1..].char_indices();

    while let Some((i, c)) = chars.next() {
        match c {
            '\n' | '\t' => continue,
            '\\' => {
                if let Some((j, e)) = chars.next() {
                    if let Some(u) = unescape_char(e) {
                        s.push(u)
                    } else {
                        SrcPos::new_pos(src, start + 1 + j).error(UnknownEscape)
                    }
                } else {
                    SrcPos::new_pos(src, start + 1 + i).error(InvalidEscapeSeq)
                }
            }
            '"' => return (Token::Str(Cow::Owned(s)), i + 2),
            _ => s.push(c),
        }
    }
    SrcPos::new_pos(src, start).error(UntermStr)
}

/// Tokenize the raw string literal in `src` at `start`.
/// Return the `Token` and it's length, including delimiting characters, in the source.
fn tokenize_raw_str_lit(src: &str, start: usize) -> (Token, usize) {
    let str_src = &src[start + 1..];
    let n_delim_octothorpes = str_src.chars().take_while(|&c| c == '#').count();

    if !str_src[n_delim_octothorpes..].starts_with('"') {
        SrcPos::new_pos(src, start).error(InvalidStrDelim)
    }

    let delim_octothorpes = &str_src[..n_delim_octothorpes];

    let str_body_src = &str_src[n_delim_octothorpes + 1..];
    for (i, c) in str_body_src.char_indices() {
        if c == '"' && str_body_src[i + 1..].starts_with(delim_octothorpes) {
            // octothorpes before and after + 'r' + open and end quotes + str len
            let literal_len = n_delim_octothorpes * 2 + 3 + i;
            return (Token::Str(Cow::Borrowed(&str_body_src[..i])), literal_len);
        }
    }
    SrcPos::new_pos(src, start).error(UntermStr)
}

/// Tokenize the numeric literal in `src` at `start`.
/// Return the `Token` and it's length in the source.
///
/// # Panics
/// Panics if the literal is not a valid numeric literal
fn tokenize_num_lit(src: &str, start: usize) -> (Token, usize) {
    let src_num = &src[start..];
    let mut has_decimal_pt = false;
    let mut has_e = false;
    let mut has_x = false;
    let mut prev_was_e = false;

    for (i, c) in src_num.char_indices() {
        match c {
            '_' => (),
            'E' if !has_e => {
                has_e = true;
                prev_was_e = true
            }
            'x' if !has_x => has_x = true,
            '-' if prev_was_e => (),
            _ if c.is_numeric() => (),
            '.' if !has_decimal_pt => has_decimal_pt = true,
            _ if is_delim_char(c) => return (Token::Num(&src_num[..i]), i),
            _ => break,
        }
        if c != 'E' {
            prev_was_e = false;
        }
    }
    SrcPos::new_pos(src, start).error(InvalidNum)
}

/// Returns whether `c` delimits tokens
fn is_delim_char(c: char) -> bool {
    match c {
        '(' | ')' | '[' | ']' | '{' | '}' | ';' => true,
        _ if c.is_whitespace() => true,
        _ => false,
    }
}

/// Returns whether `c` is a valid character of an ident
fn is_ident_char(c: char) -> bool {
    match c {
        '\'' | '"' => false,
        _ if is_delim_char(c) => false,
        _ => true,
    }
}

/// Tokenize the numeric literal in `src` at `start`.
/// Return the `Token` and it's length in the source.
///
/// # Panics
/// Panics if the literal is not a valid numeric literal
fn tokenize_ident(src: &str, start: usize) -> (Token, usize) {
    let src_ident = &src[start..];
    for (i, c) in src_ident.char_indices() {
        if is_delim_char(c) {
            return (Token::Ident(&src_ident[..i]), i);
        } else if !is_ident_char(c) {
            break;
        }
    }
    SrcPos::new_pos(src, start).error(InvalidIdent)
}

/// An iterator of `Token`s and their position in some source code
#[derive(Debug)]
struct Tokens<'src> {
    src: &'src str,
    pos: usize,
}
impl<'src> From<&'src str> for Tokens<'src> {
    fn from(src: &'src str) -> Tokens {
        Tokens { src: src, pos: 0 }
    }
}
impl<'src> Iterator for Tokens<'src> {
	type Item = (Token<'src>, SrcPos<'src>);

    fn next(&mut self) -> Option<(Token<'src>, SrcPos<'src>)> {
        let pos = self.pos;
        let mut chars = self.src[pos..]
                            .char_indices()
                            .map(|(n, c)| (pos + n, c));

        while let Some((i, c)) = chars.next() {
            let (token, len) = match c {
                _ if c.is_whitespace() => continue,
                ';' => {
                    while let Some((_, c)) = chars.next() {
                        if c == '\n' {
                            break;
                        }
                    }
                    continue;
                }
                '\'' => (Token::Quote, 1),
                '(' => (Token::LParen, 1),
                ')' => (Token::RParen, 1),
                '"' => tokenize_str_lit(self.src, i),
                'r' if self.src[i + 1..].starts_with(|c: char| c == '"' || c == '#') => {
                    tokenize_raw_str_lit(self.src, i)
                }
                _ if c.is_numeric() => tokenize_num_lit(self.src, i),
                _ if is_ident_char(c) => tokenize_ident(self.src, i),
                _ => SrcPos::new_pos(self.src, i).error(Unexpected("character")),
            };

            self.pos = i + len;
            return Some((token, SrcPos::new_interval(self.src, i, self.pos)));
        }
        None
    }
}

/// A tree of lists, identifiers, and literals
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenTree<'src> {
    List(Vec<TokenTreeMeta<'src>>),
    Ident(&'src str),
    Num(&'src str),
    Str(Cow<'src, str>),
}
impl<'src> TokenTree<'src> {
    pub fn get_ident(&self) -> Option<&str> {
        match *self {
            TokenTree::Ident(ident) => Some(ident),
            _ => None,
        }
    }
}

/// A `TokenTree` with meta-data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenTreeMeta<'src> {
    pub tt: TokenTree<'src>,
    pub pos: SrcPos<'src>,
}
impl<'src> TokenTreeMeta<'src> {
    /// Construct a new `TokenTreeMeta` from a `TokenTree` and a source position
    pub fn new(tt: TokenTree<'src>, pos: SrcPos<'src>) -> Self {
        TokenTreeMeta { tt: tt, pos: pos }
    }

    pub fn new_list(tts: Vec<TokenTreeMeta<'src>>, pos: SrcPos<'src>) -> Self {
        TokenTreeMeta {
            tt: TokenTree::List(tts),
            pos: pos,
        }
    }

    pub fn list_len(&self) -> Option<usize> {
        match self.tt {
            TokenTree::List(ref list) => Some(list.len()),
            _ => None,
        }
    }

    /// Construct a new `TokenTreeMeta` from a token with a position, and the tokens following
    fn from_token((token, mut pos): (Token<'src>, SrcPos<'src>), nexts: &mut Tokens<'src>) -> Self {
        let tt = match token {
            Token::LParen => {
                let (list, end) = tokens_to_trees_until(nexts, Some((pos.clone(), &Token::RParen)));
                pos.end = end;
                TokenTree::List(list)
            }
            Token::Ident(ident) => TokenTree::Ident(ident),
            Token::Num(num) => TokenTree::Num(num),
            Token::Str(s) => TokenTree::Str(s),
            Token::Quote => {
                TokenTree::List(vec![TokenTreeMeta::new(TokenTree::Ident("quote"), pos.clone()),
                                     TokenTreeMeta::from_token(nexts.next().unwrap_or_else(|| {
                                                                   pos.error(Unexpected("quote"))
                                                               }),
                                                               nexts)])
            }
            _ => pos.error(Unexpected("token")),
        };
        TokenTreeMeta::new(tt, pos)
    }

    pub fn add_expansion_site(&mut self, exp: &SrcPos<'src>) {
        self.pos.add_expansion_site(exp);

        if let TokenTree::List(ref mut list) = self.tt {
            for li in list {
                li.add_expansion_site(exp)
            }
        }
    }
}

/// Construct trees from `tokens` until a lone `delim` is encountered.
///
/// Returns trees and index of closing delimiter if one was supplied.
fn tokens_to_trees_until<'src>(tokens: &mut Tokens<'src>,
                               start_and_delim: Option<(SrcPos, &Token)>)
                               -> (Vec<TokenTreeMeta<'src>>, Option<usize>) {
    let (start, delim) = start_and_delim.map(|(s, t)| (Some(s), Some(t)))
                                        .unwrap_or((None, None));

    let mut tts = Vec::new();

    while let Some((token, t_pos)) = tokens.next() {
        if Some(&token) == delim {
            return (tts, t_pos.end);
        } else {
            tts.push(TokenTreeMeta::from_token((token, t_pos), tokens))
        }
    }
    match start {
        None => (tts, None),
        Some(pos) => pos.error(UndelimItem),
    }
}

/// Represent some source code as `TokenTreeMeta`s
pub fn token_trees_from_src(src: &str) -> Vec<TokenTreeMeta> {
    tokens_to_trees_until(&mut Tokens::from(src), None).0
}

#[cfg(test)]
mod test {
    use super::*;
    use super::Token::*;
}
