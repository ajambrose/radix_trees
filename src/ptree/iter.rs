use super::PTreeMap;
use super::node::Link;
use super::utils::KeyMask;
use crate::TrieKey;
use core::{iter::FusedIterator, marker::PhantomData};

impl<K: TrieKey, V> IntoIterator for PTreeMap<K, V> {
    type IntoIter = IntoIter<K, V>;
    type Item = (KeyMask<K>, V);

    /// Creates a consuming iterator that moves each [`KeyMask`]-value pair out of the trie.
    ///
    /// The iterator will yield items in lexical order of keys.
    ///
    /// # Examples
    /// ```
    /// use radix_trees::ptree::PTreeMap;
    /// use radix_trees::ptree::KeyMask;
    ///
    /// let keys = ["Hello", "Hello world!", "Ferris", "Ferris Bueller"].map(KeyMask::new);
    /// let vals = [0u32, 1, 2, 3];
    /// let mut expected: Vec<_> = keys.iter().cloned().zip(vals).collect();
    /// let t: PTreeMap<_, _> = expected.iter().cloned().collect();
    /// expected.sort_by(|(km1, _), (km2, _)| km1.cmp(km2)); // sort according to key/mask lexical ordering
    /// assert_eq!(t.into_iter().collect::<Vec<_>>(), expected);
    /// ```
    fn into_iter(mut self) -> Self::IntoIter {
        let curr = core::mem::replace(&mut self.root, Link::null());
        let len = core::mem::replace(&mut self.len, 0);
        IntoIter { curr, len, _pd: PhantomData }
    }
}

/// An owning iterator over the entries of a [`PTreeMap`] in lexical order.
///
/// Created by calling [`PTreeMap::into_iter`].
pub struct IntoIter<K: TrieKey, V> {
    pub(super) curr: Link<K, V>,
    pub(super) len: usize,
    pub(super) _pd: PhantomData<(K, V)>,
}

/// Drops any remaining un-yielded elements held by the iterator.
impl<K: TrieKey, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

impl<K: TrieKey, V> Iterator for IntoIter<K, V> {
    type Item = (KeyMask<K>, V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.curr.get_mut() {
            if let Some(val) = node.val.take() {
                let kv = *val;
                self.len -= 1;
                // SAFETY: The presence of this key/mask in the trie means that it was already validated
                return Some((unsafe { KeyMask::new_unchecked(kv.0, node.masklen) }, kv.1));
            }

            let (next, parent_cnode) = if !node.left.is_null() {
                (node.left, Link::null())
            } else if !node.right.is_null() {
                (node.right, Link::null())
            } else {
                let next = node.parent;
                if let Some(p) = next.get_mut() {
                    if node.is_right_child {
                        (next, core::mem::replace(&mut p.right, Link::null()))
                    } else {
                        (next, core::mem::replace(&mut p.left, Link::null()))
                    }
                } else {
                    (next, self.curr)
                }
            };

            parent_cnode.free();
            self.curr = next;
        }
        assert_eq!(self.len, 0);
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: TrieKey, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K: TrieKey, V> FusedIterator for IntoIter<K, V> {}

impl<K: TrieKey, V> FromIterator<(K, V)> for PTreeMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut t = PTreeMap::new();
        t.extend(iter);
        t
    }
}

impl<K: TrieKey, V> FromIterator<(KeyMask<K>, V)> for PTreeMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (KeyMask<K>, V)>>(iter: T) -> Self {
        let mut t = PTreeMap::new();
        t.extend(iter);
        t
    }
}

impl<K: TrieKey, V> Extend<(K, V)> for PTreeMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(km, v)| drop(self.insert(km, v)));
    }
}

impl<K: TrieKey, V> Extend<(KeyMask<K>, V)> for PTreeMap<K, V> {
    fn extend<T: IntoIterator<Item = (KeyMask<K>, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(km, v)| drop(self.insert_exact(km, v)));
    }
}

impl<'a, K: TrieKey, V> IntoIterator for &'a PTreeMap<K, V> {
    type IntoIter = Iter<'a, K, V>;
    type Item = (KeyMask<&'a K>, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the entries of a [`PTreeMap`] in lexical order.
///
/// Created by calling [`PTreeMap::iter`].
pub struct Iter<'a, K: TrieKey, V> {
    pub(super) curr: Link<K, V>,
    pub(super) len: usize,
    pub(super) _pd: PhantomData<&'a (K, V)>,
}

impl<'a, K: TrieKey, V> Iter<'a, K, V> {
    /// Creates an iterator which [`clone`](core::clone::Clone::clone)s all of its elements.
    ///
    /// This is separate from the core iterator [`cloned`](core::iter::Iterator::cloned) function,
    /// as it allows an iterator of [`KeyMask<&K>`] to be cloned to [`KeyMask<K>`].
    pub fn cloned(self) -> Cloned<Self>
    where
        K: Clone,
        V: Clone,
    {
        Cloned { it: self }
    }

    /// Creates an iterator which copies all of its elements.
    ///
    /// This is separate from the core iterator [`copied`](core::iter::Iterator::copied) function,
    /// as it allows an iterator of [`KeyMask<&K>`] to be copied to [`KeyMask<K>`].
    pub fn copied(self) -> Copied<Self>
    where
        K: Copy,
        V: Copy,
    {
        Copied { it: self }
    }
}

impl<'a, K: TrieKey, V> Iterator for Iter<'a, K, V> {
    type Item = (KeyMask<&'a K>, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut curr = self.curr.get().expect("iterator length matches populated nodes");

        let kv = curr.val.as_deref().unwrap_or_else(|| {
            self.curr = self.curr.next_val();
            curr = self.curr.get().expect("iterator length matches populated nodes");
            curr.val.as_deref().expect("nonzero iterator length should find a node")
        });

        // SAFETY: The presence of this key/mask in the trie means that it was already validated
        let ret = Some((unsafe { KeyMask::new_unchecked(&kv.0, curr.masklen) }, &kv.1));
        self.len -= 1;

        if self.len != 0 {
            self.curr = self.curr.next_val();
        }

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: TrieKey, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K: TrieKey, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K: TrieKey, V> IntoIterator for &'a mut PTreeMap<K, V> {
    type IntoIter = IterMut<'a, K, V>;
    type Item = (KeyMask<&'a K>, &'a mut V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A mutable iterator over the entries of a [`PTreeMap`] in lexical order.
///
/// Created by [`PTreeMap::iter_mut`].
pub struct IterMut<'a, K: TrieKey, V> {
    pub(super) curr: Link<K, V>,
    pub(super) len: usize,
    pub(super) _pd: PhantomData<&'a mut (K, V)>,
}

impl<'a, K: TrieKey, V> Iterator for IterMut<'a, K, V> {
    type Item = (KeyMask<&'a K>, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut curr = self.curr.get_mut().expect("iterator length matches populated nodes");

        let kv = if curr.val.is_some() {
            curr.val.as_deref_mut().unwrap()
        } else {
            self.curr = self.curr.next_val();
            curr = self.curr.get_mut().expect("iterator length matches populated nodes");
            curr.val.as_deref_mut().expect("nonzero iterator length should find a node")
        };

        // SAFETY: The presence of this key/mask in the trie means that it was already validated
        let ret = Some((unsafe { KeyMask::new_unchecked(&kv.0, curr.masklen) }, &mut kv.1));
        self.len -= 1;

        if self.len != 0 {
            self.curr = self.curr.next_val();
        }

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: TrieKey, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K: TrieKey, V> FusedIterator for IterMut<'_, K, V> {}

/// An iterator that clones the elements of an underlying iterator.
///
/// This differs from Rust's core [`Cloned`](core::iter::Cloned) type because cloning
/// an iterator normally requires that the iterator yields references.
pub struct Cloned<I> {
    it: I,
}

impl<'a, I, K, V> Iterator for Cloned<I>
where
    I: Iterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Clone + 'a,
    V: Clone + 'a,
{
    type Item = (KeyMask<K>, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|(km, v)| (KeyMask::clone_borrowed(&km), v.clone()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<'a, I, K, V> ExactSizeIterator for Cloned<I>
where
    I: ExactSizeIterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Clone + 'a,
    V: Clone + 'a,
{
    fn len(&self) -> usize {
        self.it.len()
    }
}

impl<'a, I, K, V> FusedIterator for Cloned<I>
where
    I: FusedIterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Clone + 'a,
    V: Clone + 'a,
{
}

/// An iterator that copies the elements of an underlying iterator.
///
/// This differs from Rust's core [`Copied`](core::iter::Copied) type because copying
/// an iterator normally requires that the iterator yields references.
pub struct Copied<I> {
    it: I,
}

impl<'a, I, K, V> Iterator for Copied<I>
where
    I: Iterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Copy + 'a,
    V: Copy + 'a,
{
    type Item = (KeyMask<K>, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|(km, v)| (KeyMask::copy_borrowed(&km), *v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<'a, I, K, V> ExactSizeIterator for Copied<I>
where
    I: ExactSizeIterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Copy + 'a,
    V: Copy + 'a,
{
    fn len(&self) -> usize {
        self.it.len()
    }
}

impl<'a, I, K, V> FusedIterator for Copied<I>
where
    I: FusedIterator<Item = (KeyMask<&'a K>, &'a V)>,
    K: TrieKey + Copy + 'a,
    V: Copy + 'a,
{
}
