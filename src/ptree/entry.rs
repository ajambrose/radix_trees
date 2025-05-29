use super::PTreeMap;
use super::node::{Link, Node};
use super::utils::KeyMask;
use crate::{Equivalent, TrieKey};
use alloc::boxed::Box;
use core::borrow::Borrow;
use core::mem;

/// Stores data common between [`VacantEntry`] and [`VacantEntryRef`].
pub(super) struct VacantEntryCommon<'a, K: TrieKey, V> {
    tree: &'a mut PTreeMap<K, V>,
    masklen: u32,
    branch_masklen: u32,
    link: Link<K, V>,
    parent: Link<K, V>,
    is_right_child: bool,  // which child link is `link` referencing
    is_right_parent: bool, // for inline insertion, which link does it parent with
}

impl<'a, K: TrieKey, V> VacantEntryCommon<'a, K, V> {
    pub(super) fn new(
        tree: &'a mut PTreeMap<K, V>,
        masklen: u32,
        branch_masklen: u32,
        link: Link<K, V>,
        parent: Link<K, V>,
        is_right_child: bool,
        is_right_parent: bool,
    ) -> Self {
        Self { tree, masklen, branch_masklen, link, parent, is_right_child, is_right_parent }
    }
}

/// A handle to a vacant entry in a [`PTreeMap`]. Part of [`Entry`].
pub struct VacantEntry<'a, K: TrieKey, V> {
    common: VacantEntryCommon<'a, K, V>,
    key: K,
}

impl<'a, K: TrieKey, V> VacantEntry<'a, K, V> {
    pub(super) fn new(key: K, common: VacantEntryCommon<'a, K, V>) -> Self {
        Self { common, key }
    }

    /// Get a reference to the key that would be used when inserting a value.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Perform some runtime checks when converting to an [`OccupiedEntry`], and increment tree length.
    fn into_occupied(tree: &'a mut PTreeMap<K, V>, link: Link<K, V>) -> OccupiedEntry<'a, K, V> {
        let Some(node) = link.get() else {
            panic!("Tried to convert an unoccupied VacantEntry into an OccupiedEntry");
        };
        assert!(node.val.is_some());

        tree.len += 1;
        OccupiedEntry::new(tree, link)
    }

    /// Inserts the provided value using the [`VacantEntry`]'s key, and returns an [`OccupiedEntry`].
    pub fn insert_entry(self, val: V) -> OccupiedEntry<'a, K, V> {
        // macro to avoid partial borrow complaints
        macro_rules! add_child_link {
            ($Self:ident, $Link:ident) => {
                if let Some(p) = $Self.common.parent.get_mut() {
                    let c = if $Self.common.is_right_child { &mut p.right } else { &mut p.left };
                    *c = $Link;
                } else {
                    assert!($Self.common.is_right_child); // root node always points "right"
                    $Self.common.tree.root = $Link;
                }
            };
        }

        if let Some(node) = self.common.link.get_mut() {
            assert!(node.masklen >= self.common.branch_masklen);
            if node.masklen == self.common.branch_masklen {
                // insert data at what used to be a branch node
                assert!(node.val.is_none());
                node.val = Some(Box::new((self.key, val)));
                Self::into_occupied(self.common.tree, self.common.link)
            } else if self.common.masklen <= self.common.branch_masklen {
                // insert the value in-between node and parent, with node as a single child
                let (left, right) = if self.common.is_right_parent {
                    (Link::null(), self.common.link)
                } else {
                    (self.common.link, Link::null())
                };

                let new_node = Box::new(Node {
                    val: Some(Box::new((self.key, val))),
                    masklen: self.common.branch_masklen,
                    left,
                    right,
                    parent: self.common.parent,
                    is_right_child: self.common.is_right_child,
                });

                // can't panic now, start doing all the tree fixup
                let new_node_link = Link::new(new_node);
                add_child_link!(self, new_node_link);
                node.parent = new_node_link;
                node.is_right_child = self.common.is_right_parent;

                Self::into_occupied(self.common.tree, new_node_link)
            } else {
                // create a new branch node with the new node and this existing node as children
                let new_branch = Box::new(Node {
                    val: None,
                    masklen: self.common.branch_masklen,
                    left: Link::null(),
                    right: Link::null(),
                    parent: self.common.parent,
                    is_right_child: self.common.is_right_child,
                });

                let new_node = Box::new(Node::new_leaf(
                    Some(Box::new((self.key, val))),
                    self.common.masklen,
                    Link::null(),
                    !self.common.is_right_parent,
                ));

                // can't panic now, start doing all the tree fixup
                let new_branch_link = Link::new(new_branch);
                let new_node_link = Link::new(new_node);

                let new_node = new_node_link.get_mut().unwrap();

                add_child_link!(self, new_branch_link);
                node.parent = new_branch_link;
                node.is_right_child = self.common.is_right_parent;
                new_node.parent = new_branch_link;
                let old_link = self.common.link;

                let new_branch = new_branch_link.get_mut().unwrap();
                let link = if !self.common.is_right_parent {
                    new_branch.left = old_link;
                    new_branch.right = new_node_link;
                    new_branch.right
                } else {
                    new_branch.left = new_node_link;
                    new_branch.right = old_link;
                    new_branch.left
                };

                Self::into_occupied(self.common.tree, link)
            }
        } else {
            // parent has an empty link that we can populate here
            let link = Link::new(Box::new(Node::new_leaf(
                Some(Box::new((self.key, val))),
                self.common.masklen,
                self.common.parent,
                self.common.is_right_child,
            )));
            add_child_link!(self, link);
            Self::into_occupied(self.common.tree, link)
        }
    }

    /// Inserts the provided value using the [`VacantEntry`]'s key,
    /// and returns a mutable reference to the inserted value.
    pub fn insert(self, val: V) -> &'a mut V {
        self.insert_entry(val).into_mut()
    }
}

/// A handle to a vacant entry in a [`PTreeMap`]. Part of [`EntryRef`].
///
/// Unlike [`VacantEntry`], the contained key is a reference type, and is only converted
/// to an owned value when calling one of the insertion functions.
pub struct VacantEntryRef<'a, 'b, K: TrieKey, Q: TrieKey + Equivalent<K>, V> {
    common: VacantEntryCommon<'a, K, V>,
    key: &'b Q,
}

impl<'a, 'b, K: TrieKey, Q: TrieKey + Equivalent<K>, V> VacantEntryRef<'a, 'b, K, Q, V> {
    pub(super) fn new(key: &'b Q, common: VacantEntryCommon<'a, K, V>) -> Self {
        Self { common, key }
    }

    /// Get a reference to the key that would be used when inserting a value.
    pub fn key(&self) -> &'b Q {
        self.key
    }

    /// Inserts the provided value using the [`VacantEntryRef`]'s key, and returns an [`OccupiedEntry`].
    pub fn insert_entry(self, val: V) -> OccupiedEntry<'a, K, V>
    where
        &'b Q: Into<K>,
    {
        VacantEntry::from(self).insert_entry(val)
    }

    /// Inserts the provided value using the [`VacantEntryRef`]'s key,
    /// and returns a mutable reference to the inserted value.
    pub fn insert(self, val: V) -> &'a mut V
    where
        &'b Q: Into<K>,
    {
        VacantEntry::from(self).insert(val)
    }
}

impl<'a, 'b, K: TrieKey, Q: TrieKey + Equivalent<K>, V> From<VacantEntryRef<'a, 'b, K, Q, V>>
    for VacantEntry<'a, K, V>
where
    &'b Q: Into<K>,
{
    fn from(value: VacantEntryRef<'a, 'b, K, Q, V>) -> Self {
        Self { key: value.key.into(), common: value.common }
    }
}

/// A handle to an occupied entry in a [`PTreeMap`]. Part of [`Entry`] and [`EntryRef`].
pub struct OccupiedEntry<'a, K: TrieKey, V> {
    tree: &'a mut PTreeMap<K, V>,
    link: Link<K, V>,
}

impl<'a, K: TrieKey, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(tree: &'a mut PTreeMap<K, V>, link: Link<K, V>) -> Self {
        Self { tree, link }
    }

    fn node(&self) -> &'a mut Node<K, V> {
        self.link.get_mut().unwrap()
    }

    /// Get a reference to the key in the entry.
    pub fn key(&self) -> &K {
        &self.node().val.as_deref().unwrap().0
    }

    /// Get a reference to the value in the entry.
    pub fn get(&self) -> &V {
        &self.node().val.as_deref().unwrap().1
    }

    /// Get a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntry`] which may outlive the destruction
    /// of the [`Entry`] value, see [`into_mut`](Self::into_mut).
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.node().val.as_deref_mut().unwrap().1
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in the entry,
    /// with a lifetime bound to the [`PTreeMap`] itself.
    ///
    /// If you need multiple references to the [`OccupiedEntry`], see [`get_mut`](Self::get_mut).
    pub fn into_mut(self) -> &'a mut V {
        &mut self.node().val.as_deref_mut().unwrap().1
    }

    /// Sets the value of the entry, and returns the old value.
    pub fn insert(&mut self, val: V) -> V {
        mem::replace(self.get_mut(), val)
    }

    /// Takes the value out of the entry, and returns it.
    pub fn remove_entry(self) -> (KeyMask<K>, V) {
        let node = self.node();
        let (k, v) = *node.val.take().unwrap();
        // SAFETY: The presence of this key/mask in the trie means that it was already validated
        let km = unsafe { KeyMask::new_unchecked(k, node.masklen) };
        if !node.left.is_null() {
            if node.right.is_null() {
                node.replace(node.left);
            }
        } else if !node.right.is_null() {
            node.replace(node.right);
        } else {
            let parent = node.parent;
            self.link.free();
            if let Some(parent) = parent.get_mut() {
                if parent.val.is_none() {
                    if !parent.left.is_null() {
                        assert!(parent.right.is_null());
                        parent.replace(parent.left);
                    } else if !parent.right.is_null() {
                        parent.replace(parent.right);
                    } else {
                        unreachable!()
                    }
                }
            }
        }
        self.tree.len -= 1;
        (km, v)
    }
}

/// A handle to a single entry in a [`PTreeMap`], which may either be vacant or occupied.
///
/// Created with [`entry`](PTreeMap::entry).
pub enum Entry<'a, K: TrieKey, V> {
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K: TrieKey, V> Entry<'a, K, V> {
    /// Inserts or updates the value for this entry, and returns an [`OccupiedEntry`].
    pub fn insert(self, val: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Vacant(e) => e.insert_entry(val),
            Entry::Occupied(mut e) => {
                e.insert(val);
                e
            }
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Vacant(e) => e.insert(default),
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function
    /// if empty, and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Vacant(e) => e.insert(default()),
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is unnecessary,
    /// unlike with [`or_insert_with`](Self::or_insert_with).
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Vacant(e) => {
                let val = default(e.key());
                e.insert(val)
            }
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    /// Get a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Vacant(e) => e.key(),
            Entry::Occupied(e) => e.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Vacant(_) => self,
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
        }
    }

    /// Ensures a value is in the entry by inserting one with [`default`](Default::default) if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(Default::default)
    }
}

/// A handle to a single entry in a [`PTreeMap`], which may either be vacant or occupied,
/// with any borrowed form of the map's key type.
///
/// Created with [`entry_ref`](PTreeMap::entry_ref).
///
/// [`TrieKey`] on the borrowed form of the key type must match those for the map's key type.
/// The key must also be constructible from the borrowed form with the [`From`] trait.
pub enum EntryRef<'a, 'b, K: TrieKey, Q: TrieKey + Equivalent<K>, V> {
    /// A vacant entry.
    Vacant(VacantEntryRef<'a, 'b, K, Q, V>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, 'b, K: TrieKey, Q: TrieKey + Equivalent<K>, V> EntryRef<'a, 'b, K, Q, V> {
    /// Inserts or updates the value for this entry, and returns an [`OccupiedEntry`].
    pub fn insert(self, val: V) -> OccupiedEntry<'a, K, V>
    where
        &'b Q: Into<K>,
    {
        match self {
            EntryRef::Vacant(e) => e.insert_entry(val),
            EntryRef::Occupied(mut e) => {
                e.insert(val);
                e
            }
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        &'b Q: Into<K>,
    {
        match self {
            EntryRef::Vacant(e) => e.insert(default),
            EntryRef::Occupied(e) => e.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function
    /// if empty, and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V
    where
        &'b Q: Into<K>,
    {
        match self {
            EntryRef::Vacant(e) => e.insert(default()),
            EntryRef::Occupied(e) => e.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is unnecessary,
    /// unlike with [`or_insert_with`](Self::or_insert_with).
    pub fn or_insert_with_key<F: FnOnce(&Q) -> V>(self, default: F) -> &'a mut V
    where
        &'b Q: Into<K>,
    {
        match self {
            EntryRef::Vacant(e) => {
                let val = default(e.key());
                e.insert(val)
            }
            EntryRef::Occupied(e) => e.into_mut(),
        }
    }

    /// Get a reference to this entry's key.
    pub fn key(&self) -> &Q
    where
        K: Borrow<Q>,
    {
        match self {
            EntryRef::Vacant(e) => e.key(),
            EntryRef::Occupied(e) => e.key().borrow(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            EntryRef::Vacant(_) => self,
            EntryRef::Occupied(mut e) => {
                f(e.get_mut());
                EntryRef::Occupied(e)
            }
        }
    }

    /// Ensures a value is in the entry by inserting one with [`default`](Default::default) if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
        &'b Q: Into<K>,
    {
        self.or_insert_with(Default::default)
    }
}
