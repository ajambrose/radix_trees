use core::borrow::Borrow;

#[cfg(feature = "zerocopy")]
mod zerocopy_trait;

#[cfg(not(feature = "zerocopy"))]
mod unsafe_trait;

/// Trait definition for keys which are suitable to use in one of this crate's tries.
///
/// When implementing this trait yourself, the implementing type must NOT have interior mutability.
/// Phrased differently, for a non-mutable `T`, [`key_bytes`](TrieKey::key_bytes) must always return the
/// same value for the lifetime of that `T`.
///
/// When the `zerocopy` feature is included, this crate leverages [`zerocopy`](https://docs.rs/zerocopy) to offload unsafe
/// code and provide more blanket implementations for things like arrays and slices of data.
/// When `zerocopy` is not included, only basic sized primitives (plus slices and arrays of primitives)
/// are implemented.
pub trait TrieKey {
    fn key_bytes(&self) -> &[u8];
}

/// Key equivalence trait.
///
/// This trait allows trie lookup with key types that don't exactly match the stored key.
/// For example, this allows using `&str` to search a map with `String` keys, etc.
pub trait Equivalent<K: ?Sized> {}

impl<K: TrieKey, Q: TrieKey + Borrow<K>> Equivalent<K> for Q {}

// The below don't change based on zerocopy or not, so they can be here

impl TrieKey for str {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl TrieKey for alloc::string::String {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl TrieKey for core::ffi::CStr {
    fn key_bytes(&self) -> &[u8] {
        self.to_bytes()
    }
}

impl TrieKey for alloc::ffi::CString {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<K: TrieKey + ?Sized> TrieKey for alloc::boxed::Box<K> {
    fn key_bytes(&self) -> &[u8] {
        K::key_bytes(self)
    }
}

impl<K: TrieKey + ?Sized> TrieKey for alloc::sync::Arc<K> {
    fn key_bytes(&self) -> &[u8] {
        K::key_bytes(self)
    }
}

impl<K: TrieKey> TrieKey for alloc::vec::Vec<K>
where
    [K]: TrieKey,
{
    fn key_bytes(&self) -> &[u8] {
        self.as_slice().key_bytes()
    }
}

impl<K: TrieKey + ?Sized> TrieKey for &K {
    fn key_bytes(&self) -> &[u8] {
        (**self).key_bytes()
    }
}
