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

use std::collections::hash_map::HashMap;
use std::hash::Hash;
use std::borrow::Borrow;
use std::fmt::{self, Debug};

// TODO: Consider using BTreeMap, possible perforance increase. Do benchmarks.
/// A stack of scopes of something. Fast access due to hashmaps, and guaranteed to contain no
/// duplications at any point.
///
/// Used for ConstDef:s. Only one constant can be defined for a single name at any given moment.
#[derive(Clone)]
pub struct ScopeStack<K, V>(Vec<HashMap<K, V>>);
impl<K: Hash + Eq, V> ScopeStack<K, V> {
    pub fn new() -> ScopeStack<K, V> {
        ScopeStack(Vec::new())
    }

    pub fn push(&mut self, scope: HashMap<K, V>) {
        if scope.keys().any(|key| self.contains_key(key)) {
            panic!("ScopeStack::push: Key already exists");
        }
        self.0.push(scope);
    }

    pub fn pop(&mut self) -> Option<HashMap<K, V>> {
        self.0.pop()
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.0.iter().any(|scope| scope.contains_key(key))
    }

    pub fn get_height<Q: ?Sized>(&self, key: &Q) -> Option<usize>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        for (height, scope) in self.0.iter().enumerate() {
            if scope.contains_key(key) {
                return Some(height);
            }
        }
        None
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.get_with_height(key).map(|(v, _)| v)
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.get_mut_with_height(key).map(|(v, _)| v)
    }

    pub fn get_with_height<Q: ?Sized>(&self, key: &Q) -> Option<(&V, usize)>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        for (height, scope) in self.0.iter().enumerate().rev() {
            if let Some(def) = scope.get(key) {
                return Some((def, height));
            }
        }
        None
    }

    pub fn get_mut_with_height<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut V, usize)>
        where Q: Hash + Eq,
              K: Borrow<Q>
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
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.0.get(height).and_then(|scope| scope.get(key))
    }
    pub fn get_at_height_mut<Q: ?Sized>(&mut self, key: &Q, height: usize) -> Option<&mut V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.0.get_mut(height).and_then(|scope| scope.get_mut(key))
    }

    pub fn update<Q: ?Sized>(&mut self, key: &Q, v: V) -> Option<V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        match self.get_mut(key) {
            Some(entry) => {
                *entry = v;
                None
            }
            None => Some(v),
        }
    }
}

impl<K: Debug + Hash + Eq, V: Debug> Debug for ScopeStack<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}
