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
use std::fmt::{ self, Debug };

struct BorrowGuard<
	'stack,
	K: 'stack + Hash + Eq,
	E: 'stack,
	V: 'stack,
	ItOut: Iterator<Item=(K, E)> + 'stack,
	Fi: Fn(IntoIter<K, V>) -> ItOut + 'stack
> {
	scope_stack: &'stack mut ScopeStack<K, V>,
	borrowed_map: &'stack mut HashMap<K, E>,
	f_inverse: Fi
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut>
	Drop for BorrowGuard<'a, K, E, V, ItOut, Fi>
{
	fn drop(&mut self) {
		let scope = self.scope_stack.pop().expect("BorrowGuard::drop: failed to pop stack");

		*self.borrowed_map = (self.f_inverse)(scope.into_iter()).collect();
	}
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut>
	Deref for BorrowGuard<'a, K, E, V, ItOut, Fi>
{
	type Target = ScopeStack<K, V>;
	fn deref(&self) -> &ScopeStack<K, V> { &self.scope_stack }
}
impl<'a, K: Hash + Eq, E, V, ItOut: Iterator<Item=(K, E)>, Fi: Fn(IntoIter<K, V>) -> ItOut>
	DerefMut for BorrowGuard<'a, K, E, V, ItOut, Fi>
{
	fn deref_mut(&mut self) -> &mut ScopeStack<K, V> { self.scope_stack }
}

// TODO: Consider using BTreeMap, possible perforance increase. Do benchmarks.
/// A stack of scopes of something. Fast access due to hashmaps, and guaranteed to contain no
/// duplications at any point.
///
/// Used for ConstDef:s. Only one constant can be defined for a single name at any given moment.
pub struct ScopeStack<K, V>(
	Vec<HashMap<K, V>>
);
impl<K: Hash + Eq, V> ScopeStack<K, V> {
	pub fn new() -> ScopeStack<K, V> { ScopeStack(Vec::new()) }

	fn split_from(&mut self, from: usize) -> Vec<HashMap<K, V>> { self.0.split_off(from) }

	pub fn push(&mut self, scope: HashMap<K, V>) {
		if scope.keys().any(|key| self.contains_key(key)) {
			panic!("ScopeStack::push: Key already exists");
		}
		self.0.push(scope);
	}

	pub fn pop(&mut self) -> Option<HashMap<K, V>> { self.0.pop() }

	fn extend<I: IntoIterator<Item=HashMap<K, V>>>(&mut self, scopes: I) {
		for scope in scopes {
			self.push(scope);
		}
	}

	/// Borrows a `HashMap<K, E>`, maps it to a `HashMap<K, V>`,
	/// then pushes it onto the stack as a scope.
	/// When the returned `BorrowGuard` goes out of scope, pop and replace back the borrowed map.
	pub fn map_push_local<'a, E, ItIn, F, ItOut, Fi>(&'a mut self,
		borrowed: &'a mut HashMap<K, E>,
		map_f: F,
		map_f_inverse: Fi
	) -> BorrowGuard<K, E, V, ItOut, Fi>
		where
			ItIn: Iterator<Item=(K, V)>,
			ItOut: Iterator<Item=(K, E)>,
			F: Fn(IntoIter<K, E>) -> ItIn,
			Fi: Fn(IntoIter<K, V>) -> ItOut
	{
		let map = replace(borrowed, HashMap::new());

		self.push(HashMap::from_iter(map_f(map.into_iter())));

		BorrowGuard{ scope_stack: self, borrowed_map: borrowed, f_inverse: map_f_inverse }
	}

	pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where Q: Hash + Eq, K: Borrow<Q> {
		self.0.iter().any(|scope| scope.contains_key(key))
	}

	pub fn get_height<Q: ?Sized>(&self, key: &Q) -> Option<usize> where Q: Hash + Eq, K: Borrow<Q> {
		for (height, scope) in self.0.iter().enumerate() {
			if scope.contains_key(key) {
				return Some(height);
			}
		}
		None
	}

	pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		self.get_with_height(key).map(|(v, _)| v)
	}

	pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		self.get_mut_with_height(key).map(|(v, _)| v)
	}

	pub fn get_with_height<Q: ?Sized>(&self, key: &Q) -> Option<(&V, usize)>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		for (height, scope) in self.0.iter().enumerate().rev() {
			if let Some(def) = scope.get(key) {
				return Some((def, height));
			}
		}
		None
	}

	pub fn get_mut_with_height<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut V, usize)>
		where Q: Hash + Eq, K: Borrow<Q>
	{
		for (height, scope) in self.0.iter_mut().enumerate().rev() {
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
	pub fn do_for_item_at_height<Q: ?Sized, R, F>(&mut self, key: &Q, height: usize, action: F) -> R
		where Q: Hash + Eq + Debug, K: Borrow<Q>, V: Debug, F: Fn(&mut Self, &mut V) -> R
	{
		let mut item = match self.get_at_height_mut(key, height) {
			Some(item) => replace(item, None)
				.expect("ScopeStack::do_for_item_at_height: Item was `None`"),
			None => panic!("ScopeStack::do_for_item_at_height: Already using item")
		};

		let above = self.split_from(height + 1);

		let result = action(self, &mut item);

		*self.get_at_height_mut(key, height)
			.expect(&format!("ScopeStack::do_for_item_at_height: key `{:?}` not found", key))
			= Some(item);

		self.extend(above);

		result
	}
}
impl<K: Debug + Hash + Eq, V: Debug> Debug for ScopeStack<K, V> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		Debug::fmt(&self.0, f)
	}
}
