use crate::TrieKey;
use std::ptr::NonNull;

pub(crate) struct Node<K: TrieKey, V> {
    pub(crate) val: Option<Box<(K, V)>>,
    pub(crate) masklen: u32,
    pub(crate) left: Link<K, V>,
    pub(crate) right: Link<K, V>,
    pub(crate) parent: Link<K, V>,
    pub(crate) is_right_child: bool,
}

impl<K: TrieKey, V> Node<K, V> {
    pub(crate) fn new_leaf(
        val: Option<Box<(K, V)>>,
        masklen: u32,
        parent: Link<K, V>,
        is_right_child: bool,
    ) -> Self {
        Self {
            val,
            masklen,
            left: Link::null(),
            right: Link::null(),
            parent,
            is_right_child,
        }
    }

    pub(crate) fn replace(&mut self, other_link: Link<K, V>) {
        let other = other_link.get_mut().unwrap();
        std::mem::swap(self, other);
        self.parent = other.parent;
        self.is_right_child = other.is_right_child;
        other_link.free();
    }
}

pub(crate) struct Link<K: TrieKey, V> {
    inner: Option<NonNull<Node<K, V>>>,
}

impl<K: TrieKey, V> std::fmt::Debug for Link<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "Link({:#018x})",
            self.inner.map(|p| p.as_ptr() as usize).unwrap_or(0)
        )
    }
}

impl<K: TrieKey, V> Clone for Link<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: TrieKey, V> Copy for Link<K, V> {}

impl<K: TrieKey, V> Link<K, V> {
    pub(crate) fn new(v: Box<Node<K, V>>) -> Self {
        Self {
            inner: Some(Box::leak(v).into()),
        }
    }

    pub(crate) fn null() -> Self {
        Self { inner: None }
    }

    pub(crate) fn is_null(self) -> bool {
        self.inner.is_none()
    }

    pub(crate) fn get<'a>(self) -> Option<&'a Node<K, V>> {
        // SAFETY:
        // Links always point to valid memory, when not `None`
        self.inner.map(|p| unsafe { &*p.as_ptr() })
    }

    pub(crate) fn get_mut<'a>(self) -> Option<&'a mut Node<K, V>> {
        // SAFETY:
        // Links always point to valid memory, when not `None`
        self.inner.map(|p| unsafe { &mut *p.as_ptr() })
    }

    pub(crate) fn free(self) {
        if let Some(p) = self.inner {
            // SAFETY:
            // Links always point to valid memory, when not `None`
            let _ = unsafe { Box::from_raw(p.as_ptr()) };
        }
    }

    pub(crate) fn next(self) -> Self {
        if let Some(n) = self.get() {
            if !n.left.is_null() {
                n.left
            } else if !n.right.is_null() {
                n.right
            } else {
                let mut curr = n;
                let mut parent = n.parent;

                while let Some(p) = parent.get() {
                    if !curr.is_right_child && !p.right.is_null() {
                        return p.right;
                    }
                    curr = p;
                    parent = p.parent;
                }
                Link::null()
            }
        } else {
            Link::null()
        }
    }

    pub(crate) fn next_val(self) -> Self {
        let mut curr = self.next();
        while let Some(n) = curr.get() {
            if n.val.is_some() {
                return curr;
            } else {
                curr = curr.next();
            }
        }
        Self::null()
    }
}
