use super::TrieKey;
use zerocopy::{Immutable, IntoBytes};

#[macro_export]
/// Safely implement [`TrieKey`] for a type which already implements [`IntoBytes`] + [`Immutable`].
///
/// Only available with crate feature `zerocopy`.
macro_rules! impl_from_zerocopy {
    ($($Ty:ty),+) => {
        $(
            impl TrieKey for $Ty
            where
                $Ty: IntoBytes + Immutable,
            {
                fn key_bytes(&self) -> &[u8] {
                    self.as_bytes()
                }
            }
        )+
    }
}

// Primitives
impl_from_zerocopy!(
    bool, char, f32, f64, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
);

macro_rules! impl_zerocopy_endians {
    ($($Ty:ident),+) => {
        $(
            impl<O> TrieKey for ::zerocopy::byteorder::$Ty<O> {
                fn key_bytes(&self) -> &[u8] {
                    self.as_bytes()
                }
            }
        )+
    }
}

impl_zerocopy_endians!(F32, F64, I16, I32, I64, I128, Isize, U16, U32, U64, U128, Usize);

impl<K: IntoBytes + Immutable + TrieKey> TrieKey for zerocopy::Unalign<K> {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<K: IntoBytes + Immutable + TrieKey> TrieKey for [K] {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<K: IntoBytes + Immutable + TrieKey, const N: usize> TrieKey for [K; N] {
    fn key_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}
