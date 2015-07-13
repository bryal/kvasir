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

use std::collections::{ HashMap, HashSet };
use std::iter::once;

use lib::{ ScopeStack, error_in_source_at };
use super::lex::TokenTree;

type Macros<'a> = ScopeStack<&'a str, MacroRules<'a>>;

/// A `MacroPattern` created as part of a macro definition is guaranteed to be valid
#[derive(Clone, Debug)]
enum MacroPattern<'a> {
	Ident(&'a str),
	List(Vec<MacroPattern<'a>>),
}
impl<'a> MacroPattern<'a> {
	fn new(tt: (TokenTree, usize)) -> Result<MacroPattern, (String, usize)> {
		match tt {
			(TokenTree::Ident(ident), _) => Ok(MacroPattern::Ident(ident)),
			(TokenTree::List(list), _) => list.into_iter()
				.map(MacroPattern::new)
				.collect::<Result<_, _>>()
				.map(MacroPattern::List),
			(_, pos) => Err(("Expected list or ident".into(), pos))
		}
	}
	/// Check whether the provided `TokenTree` matches the pattern `self`
	fn matches(&self, arg: &TokenTree<'a>, literals: &HashSet<&'a str>) -> bool {
		match (self, arg) {
			(&MacroPattern::Ident(ref pi), &TokenTree::Ident(ref ti)) if literals.contains(pi) =>
				pi == ti,
			(&MacroPattern::Ident(_), _) => true,
			(&MacroPattern::List(ref patts), &TokenTree::List(ref sub_args))
				if patts.len() == sub_args.len()
			=>
				patts.iter().zip(sub_args).all(|(patt, &(ref sub_arg, _))|
					patt.matches(sub_arg, literals)),
			_ => false,
		}
	}

	/// Bind the `TokenTree`, `arg`, to the pattern `self`
	///
	/// # Panics
	/// Panics on pattern mismatch and on invalid pattern
	fn bind(&self, arg: TokenTree<'a>, literals: &HashSet<&'a str>)
		-> HashMap<&'a str, TokenTree<'a>>
	{
		let mut map: HashMap<&str, _> = HashMap::with_capacity(1);

		match *self {
			MacroPattern::Ident(pi) => match arg {
				TokenTree::Ident(ti) if literals.contains(pi) && pi == ti => (),
				_ if literals.contains(pi) =>
					panic!("bind_pattern: Pattern mismatch. Expected literal ident"),
				arg => { map.insert(pi, arg); },
			},
			MacroPattern::List(ref patts) => if let TokenTree::List(sub_args) = arg {
				map.extend(patts.iter()
					.zip(sub_args)
					.flat_map(|(patt, (sub_arg, _))| patt.bind(sub_arg, literals)))
			} else {
				panic!("bind_pattern: Pattern mismatch")
			},
		}

		map
	}
}

#[derive(Clone, Debug)]
struct MacroRules<'a> {
	literals: HashSet<&'a str>,
	rules: Vec<(MacroPattern<'a>, (TokenTree<'a>, usize))>,
}
impl<'a> MacroRules<'a> {
	fn new<I, T>(maybe_literals: Vec<(TokenTree<'a>, usize)>, maybe_rules: T)
		-> Result<MacroRules<'a>, (String, usize)>
		where
			I: Iterator<Item=(TokenTree<'a>, usize)>,
			T: IntoIterator<IntoIter=I, Item=(TokenTree<'a>, usize)>
	{
		let literals = try!(maybe_literals.into_iter()
			.map(|(item, pos)| match item {
				TokenTree::Ident(lit) => Ok(lit),
				_ => Err(("Expected literal ident".into(), pos)),
			})
			.collect::<Result<HashSet<_>, _>>());

		let mut rules = Vec::with_capacity(1);

		for (maybe_rule, pos) in maybe_rules {
			if let TokenTree::List(mut rule) = maybe_rule {
				if rule.len() != 2 {
					return Err(("Invalid rule".into(), pos));
				}

				let template = rule.pop().unwrap();
				let pattern = try!(MacroPattern::new(rule.pop().unwrap()));

				rules.push((pattern, template))
			} else {
				return Err(("Invalid rule".into(), pos))
			}
		}

		Ok(MacroRules{ literals: literals, rules: rules })
	}

	fn apply_to(&self, args: Vec<(TokenTree<'a>, usize)>, pos: usize, macros: &mut Macros<'a>)
		-> Result<TokenTree<'a>, (String, usize)>
	{
		let args = TokenTree::List(args);
		for &(ref pattern, ref template) in &self.rules {
			if ! pattern.matches(&args, &self.literals) {
				continue;
			}
			
			return template.0
				.clone()
				.expand_macros(macros, &pattern.bind(args, &self.literals))
		}

		Err(("No rule matched in macro invocation".into(), pos))
	}
}

impl<'a> TokenTree<'a> {
	fn substitute_syntax_vars(self, syntax_vars: &HashMap<&str, TokenTree<'a>>) -> TokenTree<'a> {
		match self {
			TokenTree::Ident(ident) => syntax_vars.get(ident).cloned().unwrap_or(self),
			TokenTree::List(list) => TokenTree::List(
				list.map_in_place(|(e, pos)| (e.substitute_syntax_vars(syntax_vars), pos))),
			_ => self,
		}
	}

	fn expand_macros(self, macros: &mut Macros<'a>, syntax_vars: &HashMap<&'a str, TokenTree<'a>>)
		-> Result<TokenTree<'a>, (String, usize)>
	{
		match self {
			TokenTree::Ident(ident) if syntax_vars.contains_key(ident) =>
				syntax_vars[ident].clone().expand_macros(macros, &HashMap::new()),
			TokenTree::List(ref l) if l.len() == 0 => Ok(TokenTree::List(l.clone())),
			TokenTree::List(mut sexpr) => match sexpr[0] {
				(TokenTree::Ident("quote"), _) => Ok(TokenTree::List(sexpr)),
				(TokenTree::Ident("begin"), pos) =>
					expand_macros_in_scope(sexpr.drain(1..), macros, syntax_vars)
						.map(|expanded| TokenTree::List(
							once((TokenTree::Ident("begin"), pos)).chain(expanded).collect())),
				(TokenTree::Ident(macro_name), pos) if macros.contains_key(macro_name) => {
					let macro_rules = macros.get(macro_name).unwrap().0.clone();

					let args = sexpr.drain(1..)
						.map(|(arg, p)| (arg.substitute_syntax_vars(syntax_vars), p))
						.collect();
					macro_rules.apply_to(args, pos, macros)
				},
				_ => sexpr.into_iter()
					.map(|(arg, p)| arg.expand_macros(macros, syntax_vars).map(|e| (e, p)))
					.collect::<Result<_, _>>()
					.map(TokenTree::List),
			},
			_ => Ok(self),
		}
	}
}

// Expand macros in a block (lexical scope) of token trees
fn expand_macros_in_scope<'a, I, T>(
	scope_items: T,
	macros: &mut Macros<'a>,
	syntax_vars: &HashMap<&'a str, TokenTree<'a>>
) -> Result<Vec<(TokenTree<'a>, usize)>, (String, usize)>
	where
		I: Iterator<Item=(TokenTree<'a>, usize)>,
		T: IntoIterator<IntoIter=I, Item=(TokenTree<'a>, usize)>
{
	let mut local_macros = HashMap::new();
	let scope_items = scope_items.into_iter();

	// Macro definitions filtered out
	let mut exprs = Vec::with_capacity(scope_items.size_hint().1.unwrap_or(2));

	for (item, pos) in scope_items {
		if let TokenTree::List(mut sexpr) = item {
			if let Some(&(TokenTree::Ident("def-macro"), _)) = sexpr.first() {
				let mut parts = sexpr.drain(1..);

				let def_name = match parts.next() {
					Some((TokenTree::Ident(name), _)) => name,
					Some((_, p)) => return Err(("Invalid macro name".into(), p)),
					None => return Err(("Name missing in macro definition".into(), pos)),
				};
				let def_literals = match parts.next() {
					Some((TokenTree::List(l), _)) => l,
					Some((_, p)) => return Err(("Expected list of literals".into(), p)),
					None => return Err(("Literals list missing in macro definition".into(), pos)),
				};

				if let Some(_) = local_macros.insert(
					def_name.into(),
					try!(MacroRules::new(def_literals, parts)))
				{
					return Err((format!("Duplicate definition of macro `{}`", def_name), pos))
				}
			} else {
				exprs.push((TokenTree::List(sexpr), pos))
			}
		} else {
			exprs.push((item, pos))
		}
	}

	let mut macros = macros.push_local(&mut local_macros);

	exprs.into_iter()
		.map(|(tt, pos)| tt.expand_macros(&mut macros, syntax_vars).map(|e| (e, pos)))
		.collect()
}

pub fn expand_macros<'a>(src: &str, tts: Vec<(TokenTree<'a>, usize)>)
	-> Vec<(TokenTree<'a>, usize)>
{
	match expand_macros_in_scope(tts, &mut Macros::new(), &HashMap::new()) {
		Ok(tts) => tts,
		Err((e, pos)) => panic!(error_in_source_at(src, pos, e))
	}
}
