#![no_std]

mod entry;
mod iter;
mod key_trait;
mod node;
mod utils;

extern crate alloc;
use crate::entry::{
    Entry, EntryRef, OccupiedEntry, VacantEntry, VacantEntryCommon, VacantEntryRef,
};
use crate::iter::{Iter, IterMut};
pub use crate::key_trait::{Equivalent, TrieKey};
use crate::node::Link;
pub use crate::utils::{KeyMask, MAX_KEY_LEN_BYTES, key_masklen_check};
use crate::utils::{branch_bit, branch_masklen, key_eq};
use core::marker::PhantomData;

pub struct TrieMap<K: TrieKey, V> {
    root: Link<K, V>,
    len: usize,
    _pd: PhantomData<(K, V)>,
}

// Public API
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
        let curr = core::mem::replace(&mut self.root, Link::null());
        let len = core::mem::replace(&mut self.len, 0);
        let _ = crate::iter::IntoIter { curr, len, _pd: PhantomData };
    }

    pub fn entry(&mut self, km: KeyMask<K>) -> Entry<K, V> {
        let (key, masklen) = km.take();
        self.entry_common(key.key_bytes(), masklen)
            .map_or_else(|common| Entry::Vacant(VacantEntry::new(key, common)), Entry::Occupied)
    }

    pub fn entry_ref<'a, 'b, Q: TrieKey + Equivalent<K>>(
        &'a mut self,
        km: KeyMask<&'b Q>,
    ) -> EntryRef<'a, 'b, K, Q, V> {
        let (key, masklen) = km.take();
        self.entry_common(key.key_bytes(), masklen).map_or_else(
            |common| EntryRef::Vacant(VacantEntryRef::new(key, common)),
            EntryRef::Occupied,
        )
    }

    pub fn get_exact<Q: TrieKey + Equivalent<K>>(&self, km: KeyMask<Q>) -> Option<&V> {
        if let Some(node) = self.descend_shortcircuit(km.key().key_bytes(), km.masklen()).get() {
            if let Some(val) = node.val.as_deref() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    return Some(&val.1);
                }
            }
        }

        None
    }

    pub fn get_exact_mut<Q: TrieKey + Equivalent<K>>(&self, km: KeyMask<Q>) -> Option<&mut V> {
        if let Some(node) = self.descend_shortcircuit(km.key().key_bytes(), km.masklen()).get_mut()
        {
            if let Some(val) = node.val.as_deref_mut() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    return Some(&mut val.1);
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
        let curr = self.descend_shortcircuit(km.key().key_bytes(), km.masklen());
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

    // pub fn retain<F: FnMut(KeyMask<&K>, &mut V) -> bool>(&mut self, f: F) {
    //     todo!()
    // }

    // pub fn extract_if<F: FnMut(KeyMask<&K>, &mut V) -> bool>(&mut self, f: F) -> ExtractIf<'_, K, V, F> {
    //     todo!()
    // }

    pub fn iter(&self) -> Iter<K, V> {
        Iter { curr: self.root, len: self.len, _pd: PhantomData }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut { curr: self.root, len: self.len, _pd: PhantomData }
    }
}

// Private API
impl<K: TrieKey, V> TrieMap<K, V> {
    fn entry_common(
        &mut self,
        key: &[u8],
        masklen: u32,
    ) -> Result<OccupiedEntry<'_, K, V>, VacantEntryCommon<'_, K, V>> {
        let (mut curr, mut parent) = self.descend(key, masklen);

        let (branch_masklen, right) = if let Some(node) = curr.get() {
            let val = node.val.as_deref().unwrap();
            let branch_masklen = branch_masklen(val.0.key_bytes(), key);

            if node.masklen == masklen && branch_masklen == masklen {
                // exact match
                return Ok(OccupiedEntry::new(self, curr));
            }

            // prepare for backtrack
            let branch_masklen = core::cmp::min(masklen, branch_masklen);
            let right = branch_bit(val.0.key_bytes(), branch_masklen);
            (branch_masklen, right)
        } else if let Some(p) = parent.get() {
            // impossible to walk off the tree without parent having a value
            let val = p.val.as_deref().unwrap();
            let branch_masklen = branch_masklen(val.0.key_bytes(), key);
            if branch_masklen >= p.masklen {
                // simple case - we walked off the tree and should insert a leaf at that spot
                let is_right_child = branch_bit(key, p.masklen);
                return Err(VacantEntryCommon::new(
                    self,
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
            return Err(VacantEntryCommon::new(
                self,
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

        Err(VacantEntryCommon::new(
            self,
            masklen,
            branch_masklen,
            curr,
            parent,
            curr.get().unwrap().is_right_child,
            right,
        ))
    }

    fn descend(&self, key: &[u8], masklen: u32) -> (Link<K, V>, Link<K, V>) {
        let mut parent = Link::null();
        let mut curr = self.root;

        while let Some(node) = curr.get() {
            if node.masklen >= masklen && node.val.is_some() {
                break;
            }

            parent = curr;
            curr = if branch_bit(key, node.masklen) { node.right } else { node.left };
        }
        (curr, parent)
    }

    fn descend_shortcircuit(&self, key: &[u8], masklen: u32) -> Link<K, V> {
        let mut curr = self.root;

        while let Some(node) = curr.get() {
            if node.masklen >= masklen {
                break;
            }

            curr = if branch_bit(key, node.masklen) { node.right } else { node.left };
        }
        curr
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
