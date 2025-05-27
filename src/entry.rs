use crate::TrieMap;
use crate::node::{Link, Node};
use crate::{KeyMask, TrieKey};
use std::mem;

pub struct VacantEntry<'a, K: TrieKey, V> {
    tree: &'a mut TrieMap<K, V>,
    key: K,
    masklen: u32,
    branch_masklen: u32,
    link: Link<K, V>,
    parent: Link<K, V>,
    is_right_child: bool,  // which child link is `link` referencing
    is_right_parent: bool, // for inline insertion, which link does it parent with
}

impl<'a, K: TrieKey, V> VacantEntry<'a, K, V> {
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn new(
        tree: &'a mut TrieMap<K, V>,
        key: K,
        masklen: u32,
        branch_masklen: u32,
        link: Link<K, V>,
        parent: Link<K, V>,
        is_right_child: bool,
        is_right_parent: bool,
    ) -> Self {
        Self {
            tree,
            key,
            masklen,
            branch_masklen,
            link,
            parent,
            is_right_child,
            is_right_parent,
        }
    }

    pub fn key(&self) -> &K {
        &self.key
    }

    fn into_occupied(tree: &'a mut TrieMap<K, V>, link: Link<K, V>) -> OccupiedEntry<'a, K, V> {
        let Some(node) = link.get() else {
            panic!("Tried to convert an unoccupied VacantEntry into an OccupiedEntry");
        };
        assert!(node.val.is_some());

        tree.len += 1;
        OccupiedEntry::new(tree, link)
    }

    pub fn insert_entry(self, val: V) -> OccupiedEntry<'a, K, V> {
        // macro to avoid partial borrow complaints
        macro_rules! add_child_link {
            ($Self:ident, $Link:ident) => {
                if let Some(p) = $Self.parent.get_mut() {
                    let c = if $Self.is_right_child {
                        &mut p.right
                    } else {
                        &mut p.left
                    };
                    *c = $Link;
                } else {
                    assert!($Self.is_right_child); // root node always points "right"
                    $Self.tree.root = $Link;
                }
            };
        }

        if let Some(node) = self.link.get_mut() {
            assert!(node.masklen >= self.branch_masklen);
            if node.masklen == self.branch_masklen {
                // insert data at what used to be a branch node
                assert!(node.val.is_none());
                node.val = Some(Box::new((self.key, val)));
                Self::into_occupied(self.tree, self.link)
            } else if self.masklen <= self.branch_masklen {
                // insert the value in-between node and parent, with node as a single child
                let (left, right) = if self.is_right_parent {
                    (Link::null(), self.link)
                } else {
                    (self.link, Link::null())
                };

                let new_node = Box::new(Node {
                    val: Some(Box::new((self.key, val))),
                    masklen: self.branch_masklen,
                    left,
                    right,
                    parent: self.parent,
                    is_right_child: self.is_right_child,
                });

                // can't panic now, start doing all the tree fixup
                let new_node_link = Link::new(new_node);
                add_child_link!(self, new_node_link);
                node.parent = new_node_link;

                Self::into_occupied(self.tree, new_node_link)
            } else {
                // create a new branch node with the new node and this existing node as children
                let new_branch = Box::new(Node {
                    val: None,
                    masklen: self.branch_masklen,
                    left: Link::null(),
                    right: Link::null(),
                    parent: self.parent,
                    is_right_child: self.is_right_child,
                });

                let new_node = Box::new(Node::new_leaf(
                    Some(Box::new((self.key, val))),
                    self.masklen,
                    Link::null(),
                    !self.is_right_parent,
                ));

                // can't panic now, start doing all the tree fixup
                let new_branch_link = Link::new(new_branch);
                let new_node_link = Link::new(new_node);

                let new_node = new_node_link.get_mut().unwrap();

                add_child_link!(self, new_branch_link);
                node.parent = new_branch_link;
                node.is_right_child = self.is_right_parent;
                new_node.parent = new_branch_link;
                let old_link = self.link;

                let new_branch = new_branch_link.get_mut().unwrap();
                let link = if !self.is_right_parent {
                    new_branch.left = old_link;
                    new_branch.right = new_node_link;
                    new_branch.right
                } else {
                    new_branch.left = new_node_link;
                    new_branch.right = old_link;
                    new_branch.left
                };

                Self::into_occupied(self.tree, link)
            }
        } else {
            // parent has an empty link that we can populate here
            let link = Link::new(Box::new(Node::new_leaf(
                Some(Box::new((self.key, val))),
                self.masklen,
                self.parent,
                self.is_right_child,
            )));
            add_child_link!(self, link);
            Self::into_occupied(self.tree, link)
        }
    }

    pub fn insert(self, val: V) -> &'a mut V {
        self.insert_entry(val).into_mut()
    }
}

pub struct OccupiedEntry<'a, K: TrieKey, V> {
    tree: &'a mut TrieMap<K, V>,
    link: Link<K, V>,
    // _pd: PhantomData<&'a (K, V)>,
}

impl<'a, K: TrieKey, V> OccupiedEntry<'a, K, V> {
    pub(crate) fn new(tree: &'a mut TrieMap<K, V>, link: Link<K, V>) -> Self {
        Self {
            tree,
            link,
            // _pd: PhantomData,
        }
    }

    fn node(&self) -> &'a mut Node<K, V> {
        self.link.get_mut().unwrap()
    }

    pub fn key(&self) -> &K {
        &self.node().val.as_deref().unwrap().0
    }

    pub fn get(&self) -> &V {
        &self.node().val.as_deref().unwrap().1
    }

    pub fn get_mut(&mut self) -> &mut V {
        &mut self.node().val.as_deref_mut().unwrap().1
    }

    pub fn into_mut(self) -> &'a mut V {
        &mut self.node().val.as_deref_mut().unwrap().1
    }

    pub fn insert_entry(&mut self, val: V) -> V {
        mem::replace(self.get_mut(), val)
    }

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

pub enum Entry<'a, K: TrieKey, V> {
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K: TrieKey, V> Entry<'a, K, V> {
    pub fn insert(self, val: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Vacant(e) => e.insert_entry(val),
            Entry::Occupied(mut e) => {
                e.insert_entry(val);
                e
            }
        }
    }

    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Vacant(e) => e.insert(default),
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Vacant(e) => e.insert(default()),
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Vacant(e) => {
                let val = default(e.key());
                e.insert(val)
            }
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    pub fn key(&self) -> &K {
        match self {
            Entry::Vacant(e) => e.key(),
            Entry::Occupied(e) => e.key(),
        }
    }

    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Vacant(_) => self,
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(Default::default)
    }
}
