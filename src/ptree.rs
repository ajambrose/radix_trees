//! An implementation of a Patricia tree that provides associative storage via [`PTreeMap`].

mod entry;
mod iter;
mod node;
mod utils;

use self::node::Link;
use self::utils::{branch_bit, branch_masklen_bounded, key_eq};
use crate::{Equivalent, TrieKey};
use core::fmt::Debug;
use core::marker::PhantomData;

pub use self::entry::*;
pub use self::iter::*;
pub use self::utils::{KeyMask, MAX_KEY_LEN_BYTES};

/// An associative data structure that uses the underlying bit representation of keys
/// to store and search for values.
///
/// Valid keys implement the [`TrieKey`] trait, and are compared in big-endian order.
/// This produces the expected output when considering strings
/// (IE `"Hello"` is a prefix of `"Hello World"`), however it can produce unexpected
/// results when comparing little-endian integers. Therefore, it is recommended to use
/// fixed-endian types for keys. Values are unaffected by endianness.
///
/// # Examples
/// WIP
pub struct PTreeMap<K: TrieKey, V> {
    root: Link<K, V>,
    len: usize,
    _pd: PhantomData<(K, V)>,
}

// Public API
impl<K: TrieKey, V> PTreeMap<K, V> {
    /// Create an empty [`PTreeMap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns [`true`] if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the number of key-value pairs stored in the map.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Clears the map, dropping all elements and internal nodes.
    pub fn clear(&mut self) {
        let curr = core::mem::replace(&mut self.root, Link::null());
        let len = core::mem::replace(&mut self.len, 0);
        let _ = self::iter::IntoIter { curr, len, _pd: PhantomData };
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        self.entry_exact(KeyMask::new(key))
    }

    /// Gets the given key/mask length's corresponding entry in the map for in-place manipulation.
    pub fn entry_exact(&mut self, km: KeyMask<K>) -> Entry<'_, K, V> {
        let (key, masklen) = km.take();
        match self.entry_common(key.key_bytes(), masklen) {
            EntryCommon::Occupied(link) => Entry::Occupied(OccupiedEntry::new(self, link)),
            EntryCommon::Vacant(common) => Entry::Vacant(VacantEntry::new(self, key, common)),
        }
    }

    /// Gets the given key's corresponding entry by reference in the map for in-place manipulation.
    pub fn entry_ref<'a, 'b, Q: TrieKey + Equivalent<K>>(
        &'a mut self,
        key: &'b Q,
    ) -> EntryRef<'a, 'b, K, Q, V> {
        self.entry_ref_exact(KeyMask::new(key))
    }

    /// Gets the given key/mask length's corresponding entry by reference in the map for in-place manipulation.
    pub fn entry_ref_exact<'a, 'b, Q: TrieKey + Equivalent<K>>(
        &'a mut self,
        km: KeyMask<&'b Q>,
    ) -> EntryRef<'a, 'b, K, Q, V> {
        let (key, masklen) = km.take();
        match self.entry_common(key.key_bytes(), masklen) {
            EntryCommon::Occupied(link) => EntryRef::Occupied(OccupiedEntry::new(self, link)),
            EntryCommon::Vacant(common) => EntryRef::Vacant(VacantEntryRef::new(self, key, common)),
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but [`TrieKey`] on the borrowed form
    /// must match that of the key type.
    ///
    /// Equivalent to [`get_exact`](Self::get_exact) with a mask length that covers the entire key.
    pub fn get<Q: TrieKey + Equivalent<K>>(&self, key: Q) -> Option<&V> {
        self.get_exact(KeyMask::new(key))
    }

    /// Returns a reference to the value corresponding to the key / mask length.
    ///
    /// The key may be any borrowed form of the map's key type, but [`TrieKey`] on the borrowed form
    /// must match that of the key type.
    pub fn get_exact<Q: TrieKey + Equivalent<K>>(&self, km: KeyMask<Q>) -> Option<&V> {
        if let Some(node) = self.descend_shortcircuit(km.key().key_bytes(), km.masklen()).0.get() {
            if let Some(val) = node.val.as_deref() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    return Some(&val.1);
                }
            }
        }

        None
    }

    /// Returns a reference to the key-value-pair that best matches the provided key.
    ///
    /// The best match key is one that is a proper prefix of the provided key,
    /// with the longest mask length, and may be an exact match.
    pub fn get_best<Q: TrieKey + Equivalent<K>>(&self, key: Q) -> Option<(KeyMask<&K>, &V)> {
        self.get_best_masklen(KeyMask::new(key))
    }

    /// Returns a reference to the key-value-pair that best matches the provided key / mask length.
    ///
    /// The best match key is one that is a proper prefix of the provided key / mask,
    /// with the longest mask length, and may be an exact match.
    pub fn get_best_masklen<Q: TrieKey + Equivalent<K>>(
        &self,
        km: KeyMask<Q>,
    ) -> Option<(KeyMask<&K>, &V)> {
        let (key, masklen) = km.take();
        let (mut curr, parent) = self.descend_shortcircuit(key.key_bytes(), masklen);

        let branch_masklen = if let Some(mut node) = curr.get() {
            loop {
                if let Some(val) = node.val.as_deref() {
                    break branch_masklen_bounded(key.key_bytes(), val.0.key_bytes(), masklen);
                }
                curr = node.parent;
                if let Some(p) = curr.get() {
                    node = p;
                } else {
                    return None;
                }
            }
        } else if let Some(p) = parent.get() {
            // parent above an empty link is guaranteed to have a value
            let val = p.val.as_deref().unwrap();
            curr = parent;
            branch_masklen_bounded(key.key_bytes(), val.0.key_bytes(), masklen)
        } else {
            return None;
        };

        while let Some(node) = curr.get() {
            if node.masklen <= branch_masklen {
                if let Some(val) = node.val.as_deref() {
                    // SAFETY: The presence of this key/mask in the trie means that it was already validated
                    return Some((unsafe { KeyMask::new_unchecked(&val.0, node.masklen) }, &val.1));
                }
            }
            curr = node.parent;
        }

        None
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but [`TrieKey`] on the borrowed form
    /// must match that of the key type.
    ///
    /// Equivalent to [`get_exact_mut`](Self::get_exact_mut) with a mask length that covers the entire key.
    pub fn get_mut<Q: TrieKey + Equivalent<K>>(&self, key: Q) -> Option<&mut V> {
        self.get_exact_mut(KeyMask::new(key))
    }

    /// Returns a mutable reference to the value corresponding to the key / mask length.
    ///
    /// The key may be any borrowed form of the map's key type, but [`TrieKey`] on the borrowed form
    /// must match that of the key type.
    pub fn get_exact_mut<Q: TrieKey + Equivalent<K>>(&self, km: KeyMask<Q>) -> Option<&mut V> {
        if let Some(node) =
            self.descend_shortcircuit(km.key().key_bytes(), km.masklen()).0.get_mut()
        {
            if let Some(val) = node.val.as_deref_mut() {
                if key_eq(km.key().key_bytes(), km.masklen(), val.0.key_bytes(), node.masklen) {
                    return Some(&mut val.1);
                }
            }
        }

        None
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// Equivalent to [`insert_exact`](Self::insert_exact) with a mask length that covers the entire key.
    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        self.insert_exact(KeyMask::new(key), val)
    }

    /// Inserts a key-value pair into the map with the specified mask length.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    pub fn insert_exact(&mut self, km: KeyMask<K>, val: V) -> Option<V> {
        match self.entry_exact(km) {
            Entry::Vacant(e) => {
                e.insert_entry(val);
                None
            }
            Entry::Occupied(mut e) => Some(e.insert(val)),
        }
    }

    /// Removes a key from the map, returning the value at that key if it was previously in the map.
    ///
    /// Equivalent to [`remove_exact`](Self::remove_exact) with a mask length that covers the entire key.
    pub fn remove<Q>(&mut self, key: Q) -> Option<(KeyMask<K>, V)>
    where
        Q: TrieKey + Equivalent<K>,
    {
        self.remove_exact(KeyMask::new(key))
    }

    /// Removes a key / mask length from the map,
    /// returning the value at that key if it was previously in the map.
    pub fn remove_exact<Q>(&mut self, km: KeyMask<Q>) -> Option<(KeyMask<K>, V)>
    where
        Q: TrieKey + Equivalent<K>,
    {
        let (curr, _) = self.descend_shortcircuit(km.key().key_bytes(), km.masklen());
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

    /// An iterator visiting all [`KeyMask`]-value pairs in lexical order.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter { curr: self.root, end: self.root, len: self.len, _pd: PhantomData }
    }

    /// An iterator visiting all [`KeyMask`]-value pairs in lexical order, with mutable references to the values.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut { curr: self.root, end: self.root, len: self.len, _pd: PhantomData }
    }

    /// An iterator visiting all [`KeyMask`]-value pairs which are suffixes of the provided key
    /// in lexical order.
    ///
    /// If `include_exact` is set to `true`, and the provided key has an exact match in the [`PTreeMap`],
    /// then it will be included in the iterator.
    pub fn iter_suffixes<Q: TrieKey + Equivalent<K>>(
        &self,
        key: Q,
        include_exact: bool,
    ) -> IterSuffixes<'_, K, V> {
        self.iter_suffixes_masklen(KeyMask::new(key), include_exact)
    }

    /// An iterator visiting all [`KeyMask`]-value pairs which are suffixes of the provided key/mask length
    /// in lexical order.
    ///
    /// If `include_exact` is set to `true`, and the provided key / mask has an exact match in the [`PTreeMap`],
    /// then it will be included in the iterator.
    pub fn iter_suffixes_masklen<Q: TrieKey + Equivalent<K>>(
        &self,
        km: KeyMask<Q>,
        include_exact: bool,
    ) -> IterSuffixes<'_, K, V> {
        let (key, masklen) = km.take();
        match self.entry_common(key.key_bytes(), masklen) {
            EntryCommon::Occupied(link) => {
                // found an exact match, include it if requested otherwise step to the next value
                // either way, no additional work to do
                if include_exact {
                    IterSuffixes::new(link, link)
                } else {
                    IterSuffixes::new(link.next_val(link), link)
                }
            }
            EntryCommon::Vacant(common) => {
                if common.link.is_null() || common.masklen > common.branch_masklen {
                    // child subtree is nonexistent
                    IterSuffixes::new(Link::null(), Link::null())
                } else {
                    // backtrack gave us a parent that is a prefix of the requested key/mask, and a child that
                    // is a suffix. So, the child is the parent of the subtree containing all existing suffixes
                    IterSuffixes::new(common.link, common.link)
                }
            }
        }
    }
}

enum EntryCommon<K: TrieKey, V> {
    Occupied(Link<K, V>),
    Vacant(VacantEntryCommon<K, V>),
}

// Private API
impl<K: TrieKey, V> PTreeMap<K, V> {
    fn entry_common(&self, key: &[u8], masklen: u32) -> EntryCommon<K, V> {
        use EntryCommon as E;
        let (mut curr, mut parent) = self.descend(key, masklen);

        let (branch_masklen, right) = if let Some(node) = curr.get() {
            let val = node.val.as_deref().unwrap();
            let branch_masklen = branch_masklen_bounded(val.0.key_bytes(), key, masklen);

            if node.masklen == masklen && branch_masklen >= masklen {
                // exact match
                return E::Occupied(curr);
            }

            // prepare for backtrack
            let right = branch_bit(val.0.key_bytes(), branch_masklen);
            (branch_masklen, right)
        } else if let Some(p) = parent.get() {
            // impossible to walk off the tree without parent having a value
            let val = p.val.as_deref().unwrap();
            let branch_masklen = branch_masklen_bounded(val.0.key_bytes(), key, masklen);
            if branch_masklen >= p.masklen {
                // simple case - we walked off the tree and should insert a leaf at that spot
                let is_right_child = branch_bit(key, p.masklen);
                return E::Vacant(VacantEntryCommon::new(
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
            return E::Vacant(VacantEntryCommon::new(
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

        E::Vacant(VacantEntryCommon::new(
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
            if node.masklen >= masklen {
                if node.val.is_some() {
                    break;
                }

                // we're past the current key space, so all bits are "zero"
                parent = curr;
                curr = node.left;
            } else {
                parent = curr;
                curr = if branch_bit(key, node.masklen) { node.right } else { node.left };
            }
        }
        (curr, parent)
    }

    fn descend_shortcircuit(&self, key: &[u8], masklen: u32) -> (Link<K, V>, Link<K, V>) {
        let mut parent = Link::null();
        let mut curr = self.root;

        while let Some(node) = curr.get() {
            if node.masklen >= masklen {
                break;
            }

            parent = curr;
            curr = if branch_bit(key, node.masklen) { node.right } else { node.left };
        }
        (curr, parent)
    }
}

impl<K: TrieKey + Debug, V: Debug> Debug for PTreeMap<K, V> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_map().entries(self).finish()
    }
}

impl<K: TrieKey, V> Default for PTreeMap<K, V> {
    fn default() -> Self {
        Self { root: Link::null(), len: 0, _pd: PhantomData }
    }
}

impl<K: TrieKey, V> Drop for PTreeMap<K, V> {
    fn drop(&mut self) {
        self.clear();
    }
}
