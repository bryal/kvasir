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

use std::collections::hash_map::{ HashMap, IntoIter };
use std::iter::FromIterator;
use std::hash::Hash;
use std::mem::replace;
use std::borrow::Borrow;
use std::ops::{ Deref, DerefMut };

struct BorrowGuard<'a, K: 'a + Hash + Eq, E: 'a, V: 'a, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut> {
	scope_stack: &'a mut ScopeStack<K, V>,
	borrowed_map: &'a mut HashMap<K, E>,
	f_inverse: Fi
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut> Drop for BorrowGuard<'a, K, E, V, ItOut, Fi> {
	fn drop(&mut self) {
		*self.borrowed_map = HashMap::from_iter(
			(self.f_inverse)(self.scope_stack.pop().unwrap().into_iter())
		)
	}
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut> Deref for BorrowGuard<'a, K, E, V, ItOut, Fi> {
	type Target = ScopeStack<K, V>;
	fn deref(&self) -> &ScopeStack<K, V> { &self.scope_stack }
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut> DerefMut for BorrowGuard<'a, K, E, V, ItOut, Fi> {
	fn deref_mut(&mut self) -> &mut ScopeStack<K, V> { self.scope_stack }
}

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

	fn split_from(&mut self, from: usize) -> Vec<HashMap<K, V>> { self.0.split_off(from) }

	fn push(&mut self, scope: HashMap<K, V>) {
		if scope.keys().any(|key| self.contains_def(key)) {
			panic!("ScopeStack::push: Key already exists in scope");
		}
		self.0.push(scope);
	}

	fn pop(&mut self) -> Option<HashMap<K, V>> { self.0.pop() }

	fn extend<I: IntoIterator<Item=HashMap<K, V>>>(&mut self, scopes: I) {
		for scope in scopes {
			self.push(scope);
		}
	}

	pub fn push_local<'a>(&'a mut self, borrowed: &'a mut HashMap<K, V>)
		-> BorrowGuard<K, V, V, IntoIter<K, V>, fn(IntoIter<K, V>) -> IntoIter<K, V>>
	{
		fn identity<T>(x: T) -> T { x };

		self.push(replace(borrowed, HashMap::new()));

		BorrowGuard{
			scope_stack: self,
			borrowed_map: borrowed,
			f_inverse: identity::<IntoIter<K, V>> as fn(IntoIter<K, V>) -> IntoIter<K, V>
		}
	}

	/// Borrows a `HashMap<K, V>`, maps it to a `HashMap<K, E>`, then pushes it onto the stack.
	/// When the returned `BorrowGuard` goes out of scope, pop and replace back the borrowed map.
	pub fn map_push_local<'a, E, ItIn, F, ItOut, Fi>(&'a mut self,
		borrowed: &'a mut HashMap<K, E>,
		f: F,
		f_inverse: Fi)
			-> BorrowGuard<K, E, V, ItOut, Fi>
			where
				ItIn: Iterator<Item=(K, V)>,
				ItOut: Iterator<Item=(K, E)>,
				F: Fn(IntoIter<K, E>) -> ItIn,
				Fi: Fn(IntoIter<K, V>) -> ItOut
	{
		let map = replace(borrowed, HashMap::new());

		self.push(HashMap::from_iter(f(map.into_iter())));

		BorrowGuard{ scope_stack: self, borrowed_map: borrowed, f_inverse: f_inverse }
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
impl<K: Hash + Eq, V> ScopeStack<K, Option<V>> {
	// TODO: `action` could probably take `&mut Self`
	/// If item is already `None`, do nothing and return false.
	pub fn do_for_item_at_height<Q: ?Sized, F>(&mut self, key: &Q, height: usize, action: F)
		where Q: Hash + Eq, K: Borrow<Q>, F: Fn(&mut Self, &mut V)
	{
		let mut item = match self.get_at_height_mut(key, height) {
			Some(item) => replace(item, None)
				.expect("ScopeStack::do_for_item_at_height: Item was `None`"),
			None => panic!("ScopeStack::do_for_item_at_height: No entry for key function found")
		};

		let above = self.split_from(height + 1);

		action(self, &mut item);

		*self.get_at_height_mut(key, height).unwrap() = Some(item);

		self.extend(above);
	}
}
