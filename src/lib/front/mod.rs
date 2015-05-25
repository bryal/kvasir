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

use std::collections::HashMap;
use std::hash::Hash;
use std::borrow::Borrow;

pub use self::lex::{ tokenize_string, Token };
pub use self::ast::*;

pub mod ast;
pub mod lex;
pub mod parse;
pub mod inference;
pub mod core_lib;

/// A stack of scopes of something. Fast access due to hashmaps, and guaranteed to contain no
/// duplications at any point.
///
/// Used for ConstDef:s. Only one constant can be defined for a single name at any given moment.
pub struct ScopeStack<K, V>(
	Vec<HashMap<K, V>>
);
impl<K: Hash + Eq, V> ScopeStack<K, V> {
	pub fn new() -> ScopeStack<K, V> { ScopeStack(Vec::new()) }

	pub fn height(&self) -> usize { self.0.len() }

	pub fn split_from(&mut self, from: usize) -> Vec<HashMap<K, V>> { self.0.split_off(from) }

	pub fn push(&mut self, scope: HashMap<K, V>) {
		if scope.keys().any(|key| self.contains_def(key)) {
			panic!("ScopeStack::push: Key already exists in scope");
		}
		self.0.push(scope);
	}
	pub fn pop(&mut self) -> Option<HashMap<K, V>> { self.0.pop() }
	pub fn extend<I: IntoIterator<Item=HashMap<K, V>>>(&mut self, scopes: I) {
		for scope in scopes {
			self.push(scope);
		}
	}

	pub fn contains_def<Q: ?Sized>(&self, def_ident: &Q) -> bool where Q: Hash + Eq, K: Borrow<Q> {
		self.0.iter().any(|scope| scope.contains_key(def_ident))
	}

	pub fn get_height<Q: ?Sized>(&self, key: &Q) -> Option<usize> where Q: Hash + Eq, K: Borrow<Q> {
		for (height, scope) in self.0.iter().enumerate() {
			if scope.contains_key(key) {
				return Some(height);
			}
		}
		None
	}

	pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<(&V, usize)> where Q: Hash + Eq, K: Borrow<Q> {
		for (height, scope) in self.0.iter().enumerate() {
			if let Some(ref def) = scope.get(key) {
				return Some((def, height));
			}
		}
		None
	}
	pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut V, usize)>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		for (height, scope) in self.0.iter_mut().enumerate() {
			if let Some(def) = scope.get_mut(key) {
				return Some((def, height));
			}
		}
		None
	}

	/// Faster than `get` because only one level is searched in.
	pub fn get_at_height<Q: ?Sized>(&self, key: &Q, height: usize) -> Option<&V>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		self.0.get(height).and_then(|scope| scope.get(key))
	}
	pub fn get_at_height_mut<Q: ?Sized>(&mut self, key: &Q, height: usize) -> Option<&mut V>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		self.0.get_mut(height).and_then(|scope| scope.get_mut(key))
	}
}
