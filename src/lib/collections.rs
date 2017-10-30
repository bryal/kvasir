use std::borrow::Borrow;
use std::collections::hash_map::HashMap;
use std::fmt::{self, Debug};
use std::hash::Hash;

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

    pub fn split_off(&mut self, at: usize) -> Vec<HashMap<K, V>> {
        self.0.split_off(at)
    }

    pub fn extend(&mut self, xs: Vec<HashMap<K, V>>) {
        self.0.extend(xs)
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        self.0.iter().any(|scope| scope.contains_key(key))
    }

    pub fn get_height<Q: ?Sized>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        for (height, scope) in self.0.iter().enumerate() {
            if scope.contains_key(key) {
                return Some(height);
            }
        }
        None
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        self.get_with_height(key).map(|(v, _)| v)
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        self.get_mut_with_height(key).map(|(v, _)| v)
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        for scope in self.0.iter_mut().rev() {
            if let Some(def) = scope.remove(key) {
                return Some(def);
            }
        }
        None
    }

    pub fn get_with_height<Q: ?Sized>(&self, key: &Q) -> Option<(&V, usize)>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        for (height, scope) in self.0.iter().enumerate().rev() {
            if let Some(def) = scope.get(key) {
                return Some((def, height));
            }
        }
        None
    }

    pub fn get_mut_with_height<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut V, usize)>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        for (height, scope) in self.0.iter_mut().enumerate().rev() {
            if let Some(def) = scope.get_mut(key) {
                return Some((def, height));
            }
        }
        None
    }
}

impl<K: Debug + Hash + Eq, V: Debug> Debug for ScopeStack<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}
