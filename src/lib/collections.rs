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

struct AddMapNode<K, V> {
    key: K,
    val: V,
    /// null indicates no next node
    next: *mut Option<AddMapNode<K, V>>,
}

impl<K, V> AddMapNode<K, V> {
    fn entry<'a, Q>(&'a self, key: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q> + PartialEq<Q>,
    {
        if &self.key == key {
            Some((&self.key, &self.val))
        } else {
            unsafe { (*self.next).as_ref().and_then(|n| n.entry(key)) }
        }
    }

    fn add(&self, key: K, val: V) -> (&K, &V)
    where
        K: PartialEq<K>,
    {
        if self.key == key {
            panic!("Key already exists in map")
        } else {
            unsafe {
                match *self.next {
                    None => {
                        *self.next = Some(AddMapNode {
                            key: key,
                            val: val,
                            next: Box::into_raw(Box::new(None)),
                        });
                        let next = (*self.next).as_ref().unwrap();
                        (&next.key, &next.val)
                    }
                    Some(ref next_node) => next_node.add(key, val),
                }
            }
        }
    }
}

/// A map which can only grow.
///
/// Implemented with a linked list
pub struct AddMap<K, V> {
    next: *mut Option<AddMapNode<K, V>>,
}

impl<K, V> AddMap<K, V>
where
    K: PartialEq<K>,
{
    pub fn new() -> Self {
        AddMap { next: Box::into_raw(Box::new(None)) }
    }

    /// Get reference to key and value in map associated with `key`
    ///
    /// Executes in `O(n)` time
    pub fn entry<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + PartialEq<Q>,
    {
        unsafe { (*self.next).as_ref().and_then(|n| n.entry(key)) }
    }

    /// Returns whether the map contains `key`
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + PartialEq<Q>,
    {
        self.entry(key).is_some()
    }

    /// Insert the value `val` with key `key` in map
    ///
    /// Returns reference to entry in map.
    /// Executes in `O(n)` time
    ///
    /// # Panics
    ///
    /// Panics if `key` already exists in list
    pub fn add(&self, key: K, val: V) -> (&K, &V) {
        unsafe {
            if (*self.next).is_none() {
                *self.next = Some(AddMapNode {
                    key: key,
                    val: val,
                    next: Box::into_raw(Box::new(None)),
                });
                let next = (*self.next).as_ref().unwrap();
                (&next.key, &next.val)
            } else {
                (*self.next).as_ref().unwrap().add(key, val)
            }
        }
    }
}
