use crate::TrieKey;
use alloc::boxed::Box;
use core::ptr::NonNull;

/// An internal ptree node, with optional data.
pub(crate) struct Node<K: TrieKey, V> {
    pub(crate) val: Option<Box<(K, V)>>,
    pub(crate) masklen: u32,
    pub(crate) left: Link<K, V>,
    pub(crate) right: Link<K, V>,
    pub(crate) parent: Link<K, V>,
    pub(crate) is_right_child: bool,
}

impl<K: TrieKey, V> Node<K, V> {
    /// Create a new [`Node`] with no children.
    pub(crate) fn new_leaf(
        val: Option<Box<(K, V)>>,
        masklen: u32,
        parent: Link<K, V>,
        is_right_child: bool,
    ) -> Self {
        Self { val, masklen, left: Link::null(), right: Link::null(), parent, is_right_child }
    }

    /// Swap data with another node, fix up links, and free the other node.
    pub(crate) fn replace(&mut self, other_link: Link<K, V>) {
        let other = other_link.get_mut().unwrap();
        core::mem::swap(self, other);
        self.parent = other.parent;
        self.is_right_child = other.is_right_child;
        other_link.free();
    }
}

/// A nullable pointer to another [`Node`].
///
/// Notwithstanding dangling or aliasing references, the pointer is always valid,
/// IE there is no way to create a [`Link`] to memory that was not originally allocated as a node.
pub(crate) struct Link<K: TrieKey, V> {
    inner: Option<NonNull<Node<K, V>>>,
}

// can't derive because K/V don't necessarily implement Eq, even though that doesn't matter
impl<K: TrieKey, V> PartialEq<Link<K, V>> for Link<K, V> {
    fn eq(&self, other: &Link<K, V>) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<K: TrieKey, V> Eq for Link<K, V> {}

impl<K: TrieKey, V> core::fmt::Debug for Link<K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "Link({:#018x})", self.inner.map(|p| p.as_ptr() as usize).unwrap_or(0))
    }
}

impl<K: TrieKey, V> Clone for Link<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: TrieKey, V> Copy for Link<K, V> {}

impl<K: TrieKey, V> Link<K, V> {
    /// Create a new link from an owned [`Node`].
    pub(crate) fn new(v: Box<Node<K, V>>) -> Self {
        Self { inner: Some(Box::leak(v).into()) }
    }

    /// Create an empty link.
    pub(crate) fn null() -> Self {
        Self { inner: None }
    }

    /// Returns true if this link is empty.
    pub(crate) fn is_null(self) -> bool {
        self.inner.is_none()
    }

    /// Dereference the link and retrieve a shared reference to the underlying [`Node`].
    ///
    /// # Safety
    /// This API obtains a shared reference to the underlying node, so forming such a shared
    /// reference must be a legal operation. IE, it must point to a currently-valid allocation and
    /// must not alias a mutable reference.
    /// Calling `get` on a null reference IS safe, as it will return [`None`].
    pub(crate) fn get<'a>(self) -> Option<&'a Node<K, V>> {
        // SAFETY:
        // Links always point to valid memory, when not `None`
        self.inner.map(|p| unsafe { &*p.as_ptr() })
    }

    /// Dereference the link and retrieve a mutable reference to the underlying [`Node`].
    ///
    /// # Safety
    /// This API obtains a mutable reference to the underlying node, so forming such a mutable
    /// reference must be a legal operation. IE, it must point to a currently-valid allocation and
    /// must not alias any other references.
    /// Calling `get` on a null reference IS safe, as it will return [`None`].
    pub(crate) fn get_mut<'a>(self) -> Option<&'a mut Node<K, V>> {
        // SAFETY:
        // Links always point to valid memory, when not `None`
        self.inner.map(|p| unsafe { &mut *p.as_ptr() })
    }

    /// Attempt to free the [`Node`] pointed to by this link.
    pub(crate) fn free(self) {
        if let Some(p) = self.inner {
            // SAFETY:
            // Links always point to valid memory, when not `None`
            let _ = unsafe { Box::from_raw(p.as_ptr()) };
        }
    }

    /// Walk the tree and obtain the next valid internal node according to preorder traversal.
    pub(crate) fn next(self, end: Self) -> Self {
        if let Some(n) = self.get() {
            if !n.left.is_null() {
                n.left
            } else if !n.right.is_null() {
                n.right
            } else {
                if self == end {
                    return Self::null();
                }
                let mut curr = n;
                let mut parent = n.parent;

                loop {
                    if parent == end {
                        if curr.is_right_child {
                            return Self::null();
                        }
                        // not possible to walk up through the root without being the right child,
                        // so it must not be null
                        let p = parent.get().expect("root node is a right child");
                        return p.right;
                    } else {
                        let p = parent.get().expect("reached end before root");
                        if !curr.is_right_child && !p.right.is_null() {
                            return p.right;
                        }
                        curr = p;
                        parent = p.parent;
                    }
                }
            }
        } else {
            Self::null()
        }
    }

    /// Walk the tree and obtain the next valid data node according to preorder traversal.
    pub(crate) fn next_val(self, end: Self) -> Self {
        let mut curr = self.next(end);
        while let Some(n) = curr.get() {
            if n.val.is_some() {
                return curr;
            } else {
                curr = curr.next(end);
            }
        }
        Self::null()
    }
}
