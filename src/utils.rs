use crate::{Equivalent, TrieKey};
use core::ops::Deref;

pub const MAX_KEY_LEN_BYTES: usize = (u32::MAX as usize) >> 3;

#[derive(Debug, Clone, Copy)]
pub struct KeyMask<K: TrieKey> {
    key: K,
    masklen: u32,
}

impl<K: TrieKey> KeyMask<K> {
    pub fn new(key: K, masklen: u32) -> Result<Self, KeyMaskError> {
        if !key_masklen_check(K::key_bytes(&key), masklen) {
            return Err(KeyMaskError);
        }
        Ok(Self { key, masklen })
    }

    pub fn new_host(key: K) -> Self {
        let masklen =
            key_len_bits(key.key_bytes()).expect("key length does not exceed MAX_KEY_LIN_BYTES");
        Self { key, masklen }
    }

    /// Create a [`KeyMask`] without validating the inputs
    ///
    /// # Safety
    /// `key`'s length in bytes must not exceed [`MAX_KEY_LEN_BYTES`],
    /// `masklen` must not exceed the number of bits in `key`,
    /// `key` must have no bits set after the specified `masklen`.
    /// IE, [`key_masklen_check`] must return `true` for the provided inputs.
    pub unsafe fn new_unchecked(key: K, masklen: u32) -> Self {
        Self { key, masklen }
    }

    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn take(self) -> (K, u32) {
        (self.key, self.masklen)
    }

    pub fn masklen(&self) -> u32 {
        self.masklen
    }

    pub fn clone_borrowed<B>(other: &KeyMask<B>) -> Self
    where
        K: Clone,
        B: TrieKey + Deref<Target = K>,
    {
        Self { key: K::clone(&other.key), masklen: other.masklen }
    }

    pub fn copy_borrowed<B>(other: &KeyMask<B>) -> Self
    where
        K: Copy,
        B: TrieKey + Deref<Target = K>,
    {
        Self { key: *other.key, masklen: other.masklen }
    }
}

pub(crate) fn key_eq(lhs: &[u8], lhs_mask: u32, rhs: &[u8], rhs_mask: u32) -> bool {
    if lhs_mask == rhs_mask { branch_masklen(lhs, rhs) >= lhs_mask } else { false }
}

impl<K: TrieKey, Q: TrieKey + Equivalent<K>> PartialEq<KeyMask<Q>> for KeyMask<K> {
    fn eq(&self, other: &KeyMask<Q>) -> bool {
        key_eq(self.key.key_bytes(), self.masklen, other.key.key_bytes(), other.masklen)
    }
}

impl<K: TrieKey> Eq for KeyMask<K> {}

impl<K: TrieKey, Q: TrieKey + Equivalent<K>> PartialOrd<KeyMask<Q>> for KeyMask<K> {
    fn partial_cmp(&self, other: &KeyMask<Q>) -> Option<core::cmp::Ordering> {
        fn inner(lhs: &[u8], lhs_mask: u32, rhs: &[u8], rhs_mask: u32) -> core::cmp::Ordering {
            use core::cmp::Ordering as O;
            let branch_mask = branch_masklen(lhs, rhs);
            if lhs_mask == rhs_mask && branch_mask >= lhs_mask {
                O::Equal
            } else if lhs_mask < rhs_mask {
                if branch_mask < lhs_mask {
                    if branch_bit(lhs, branch_mask) { O::Greater } else { O::Less }
                } else {
                    O::Less
                }
            } else if branch_mask < rhs_mask {
                if branch_bit(lhs, branch_mask) { O::Greater } else { O::Less }
            } else {
                O::Greater
            }
        }

        Some(inner(self.key.key_bytes(), self.masklen, other.key.key_bytes(), other.masklen))
    }
}

impl<K: TrieKey> Ord for KeyMask<K> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // SAFETY: partial_cmp always returns `Some`
        unsafe { self.partial_cmp(other).unwrap_unchecked() }
    }
}

#[derive(Debug)]
pub struct KeyMaskError;

impl core::fmt::Display for KeyMaskError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "Key / masklen combination is invalid")
    }
}

fn key_len_bits(key: &[u8]) -> Option<u32> {
    let key_len = key.len();
    if key_len <= MAX_KEY_LEN_BYTES {
        // conversion is safe since bounds were already checked
        Some((key_len as u32) << 3)
    } else {
        None
    }
}

pub fn key_masklen_check(key: &[u8], masklen: u32) -> bool {
    let Some(max_mask) = key_len_bits(key) else {
        return false;
    };

    if masklen == max_mask {
        // a mask that covers the whole key is correct by definition
        return true;
    } else if masklen > max_mask {
        return false;
    }

    let mask_idx = (masklen >> 3) as usize;
    let mask = u8::MAX >> (masklen & 7);
    key[mask_idx] & mask == 0 && key[mask_idx + 1..].iter().copied().sum::<u8>() == 0
}

pub(crate) fn branch_bit(key: &[u8], masklen: u32) -> bool {
    let mask_idx = (masklen >> 3) as usize;
    let mask_bit = 1u8 << (7 - (masklen & 7));

    (key[mask_idx] & mask_bit) != 0
}

pub(crate) fn branch_masklen(a: &[u8], b: &[u8]) -> u32 {
    let Some((idx, (b1, b2))) = a.iter().zip(b).enumerate().find(|(_, (a, b))| a != b) else {
        // conversion is safe as any keys passed here were already validated
        return (core::cmp::min(a.len(), b.len()) as u32) << 3;
    };

    let n = b1 ^ b2;
    // conversion is safe as any keys passed here were already validated
    n.leading_zeros() + (idx << 3) as u32
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn keymask() {
        let a = [1u8, 2, 3, 0xff, 0, 0, 0, 0].as_slice();
        let b = [1u8, 2, 3, 0].as_slice();
        let c = [1u8, 2, 0xff, 0].as_slice();
        let d = [1u8, 2, 3, 0xff, 0, 0, 0, 1].as_slice();
        let x = KeyMask::new(a, 64).unwrap();
        let y = KeyMask::new(a, 32).unwrap();
        let z = KeyMask::new(b, 32).unwrap();
        let w = KeyMask::new(b, 31).unwrap();
        let v = KeyMask::new(c, 24).unwrap();
        KeyMask::new(a, 31).unwrap_err();
        KeyMask::new(a, 65).unwrap_err();
        KeyMask::new(d, 32).unwrap_err();

        assert_ne!(x, y);
        assert_eq!(y, y);
        assert!(y < x);
        assert!(x > y);
        assert!(z < y);
        assert!(y > z);
        assert!(w < y);
        assert!(y > w);
        assert!(v > y);
        assert!(y < v);
        assert_eq!(y.cmp(&y), core::cmp::Ordering::Equal);
    }

    #[test]
    fn err_display() {
        let s = alloc::format!("{}", KeyMaskError);
        assert_eq!(s, "Key / masklen combination is invalid");
    }

    #[test]
    fn test_branch_masklen() {
        let a = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let b = [1u8, 2, 3, 3, 5, 6, 7, 8];
        let c = [129u8, 2, 3, 4, 5, 6, 7, 8];
        let d = [1u8, 2, 3, 4, 5, 6, 7, 9];

        assert_eq!(branch_masklen(a.key_bytes(), b.key_bytes()), 29);
        assert_eq!(branch_masklen(a.key_bytes(), c.key_bytes()), 0);
        assert_eq!(branch_masklen(a.key_bytes(), d.key_bytes()), 63);
        assert_eq!(branch_masklen(a.key_bytes(), a.key_bytes()), 64);
    }

    #[test]
    fn test_branch_bit() {
        let a = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let b = [129u8, 2, 3, 4, 5, 6, 7, 8];
        let c = [1u8, 2, 3, 4, 5, 6, 7, 9];

        assert!(!branch_bit(a.key_bytes(), 0));
        assert!(branch_bit(b.key_bytes(), 0));
        assert!(!branch_bit(a.key_bytes(), 63));
        assert!(branch_bit(c.key_bytes(), 63));
        assert!(branch_bit(a.key_bytes(), 29));
        assert!(!branch_bit(a.key_bytes(), 30));
    }

    #[test]
    fn test_key_masklen_check() {
        let a = [1u8, 2, 3, 4, 0, 0, 0, 0];
        let b = [0u8; 8];
        let c = [u8::MAX; 8];

        assert!(key_masklen_check(a.key_bytes(), 30));
        assert!(!key_masklen_check(a.key_bytes(), 29));
        assert!(key_masklen_check(b.key_bytes(), 0));
        assert!(key_masklen_check(b.key_bytes(), 64));
        assert!(!key_masklen_check(b.key_bytes(), 65));
        assert!(!key_masklen_check(c.key_bytes(), 0));
        assert!(key_masklen_check(c.key_bytes(), 64));
        assert!(!key_masklen_check(c.key_bytes(), 65));
    }
}
