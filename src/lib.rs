mod entry;
mod iter;
mod key_trait;
mod node;
mod utils;

use crate::entry::{Entry, OccupiedEntry, VacantEntry};
use crate::iter::{Iter, IterMut};
pub use crate::key_trait::{Equivalent, TrieKey};
use crate::node::Link;
pub use crate::utils::{KeyMask, MAX_KEY_LEN_BYTES, key_masklen_check};
use crate::utils::{branch_bit, branch_masklen, key_eq};
use std::marker::PhantomData;

pub struct TrieMap<K: TrieKey, V> {
    root: Link<K, V>,
    len: usize,
    _pd: PhantomData<(K, V)>,
}

impl<K: TrieKey, V> TrieMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        let curr = std::mem::replace(&mut self.root, Link::null());
        let len = std::mem::replace(&mut self.len, 0);
        let _ = crate::iter::IntoIter { curr, len, _pd: PhantomData };
    }

    fn descend<Q: TrieKey + Equivalent<K>>(&self, km: &KeyMask<Q>) -> (Link<K, V>, Link<K, V>) {
        let mut parent = Link::null();
        let mut curr = self.root;

        while let Some(node) = curr.get() {
            if node.masklen >= km.masklen() && node.val.is_some() {
                break;
            }

            parent = curr;
            curr =
                if branch_bit(km.key().key_bytes(), node.masklen) { node.right } else { node.left };
        }
        (curr, parent)
    }

    fn descend_shortcircuit<Q: TrieKey + Equivalent<K>>(&self, km: &KeyMask<Q>) -> Link<K, V> {
        let mut curr = self.root;

        while let Some(node) = curr.get() {
            if node.masklen >= km.masklen() {
                break;
            }

            curr =
                if branch_bit(km.key().key_bytes(), node.masklen) { node.right } else { node.left };
        }
        curr
    }

    pub fn entry(&mut self, km: KeyMask<K>) -> Entry<K, V> {
        let (mut curr, mut parent) = self.descend(&km);
        let (key, masklen) = km.take();

        let (branch_masklen, right) = if let Some(node) = curr.get() {
            let val = node.val.as_deref().unwrap();
            let branch_masklen = branch_masklen(val.0.key_bytes(), key.key_bytes());

            if node.masklen == masklen && branch_masklen == masklen {
                // exact match
                return Entry::Occupied(OccupiedEntry::new(self, curr));
            }

            // prepare for backtrack
            let branch_masklen = std::cmp::min(masklen, branch_masklen);
            let right = branch_bit(val.0.key_bytes(), branch_masklen);
            (branch_masklen, right)
        } else if let Some(p) = parent.get() {
            // impossible to walk off the tree without parent having a value
            let val = p.val.as_deref().unwrap();
            let branch_masklen = branch_masklen(val.0.key_bytes(), key.key_bytes());
            if branch_masklen >= p.masklen {
                // simple case - we walked off the tree and should insert a leaf at that spot
                let is_right_child = branch_bit(key.key_bytes(), p.masklen);
                return Entry::Vacant(VacantEntry::new(
                    self,
                    key,
                    masklen,
                    masklen,
                    curr,
                    parent,
                    is_right_child,
                    false,
                ));
            } else {
                // we walked off the tree but actually the keys differ higher up; prepare for backtrack
                let right = branch_bit(val.0.key_bytes(), branch_masklen);
                curr = parent;
                parent = p.parent;
                (branch_masklen, right)
            }
        } else {
            return Entry::Vacant(VacantEntry::new(
                self,
                key,
                masklen,
                masklen,
                Link::null(),
                Link::null(),
                true,
                false,
            ));
        };

        while let Some(p) = parent.get() {
            // go until we find a node with a lesser mask length
            if p.masklen < branch_masklen {
                break;
            } else {
                curr = parent;
                parent = p.parent;
            }
        }

        Entry::Vacant(VacantEntry::new(
            self,
            key,
            masklen,
            branch_masklen,
            curr,
            parent,
            curr.get().unwrap().is_right_child,
            right,
        ))
    }

    pub fn get_exact<Q: TrieKey + Equivalent<K>>(&self, km: KeyMask<Q>) -> Option<&V> {
        if let Some(node) = self.descend_shortcircuit(&km).get() {
            if let Some(val) = node.val.as_deref() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    return Some(&val.1);
                }
            }
        }

        None
    }

    pub fn insert(&mut self, km: KeyMask<K>, val: V) -> Option<V> {
        match self.entry(km) {
            Entry::Vacant(e) => {
                e.insert_entry(val);
                None
            }
            Entry::Occupied(mut e) => Some(e.insert_entry(val)),
        }
    }

    pub fn remove<Q>(&mut self, km: KeyMask<Q>) -> Option<(KeyMask<K>, V)>
    where
        Q: TrieKey + Equivalent<K>,
    {
        let curr = self.descend_shortcircuit(&km);
        if let Some(node) = curr.get() {
            if let Some(val) = node.val.as_deref() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    let e = OccupiedEntry::new(self, curr);
                    return Some(e.remove_entry());
                }
            }
        }

        None
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter { curr: self.root, len: self.len, _pd: PhantomData }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut { curr: self.root, len: self.len, _pd: PhantomData }
    }
}

impl<K: TrieKey, V> Default for TrieMap<K, V> {
    fn default() -> Self {
        Self { root: Link::null(), len: 0, _pd: PhantomData }
    }
}

impl<K: TrieKey, V> Drop for TrieMap<K, V> {
    fn drop(&mut self) {
        self.clear();
    }
}
