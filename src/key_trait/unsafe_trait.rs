use super::TrieKey;

macro_rules! impl_unsafe_transform {
    ($($Ty:ty),+) => {
        $(
            impl TrieKey for $Ty
            {
                fn key_bytes(&self) -> &[u8] {
                    unsafe {
                        let p = self as *const Self as *const u8;
                        std::slice::from_raw_parts(p, size_of::<$Ty>())
                    }
                }
            }

            // Done manually instead of with a blanket impl since we can't guarantee there is no padding
            impl TrieKey for [$Ty]
            {
                fn key_bytes(&self) -> &[u8] {
                    unsafe {
                        let sz = std::mem::size_of_val(self);
                        let p = self.as_ptr() as *const u8;
                        std::slice::from_raw_parts(p, sz)
                    }
                }
            }

            // Done manually instead of with a blanket impl since we can't guarantee there is no padding
            impl<const N: usize> TrieKey for [$Ty; N]
            {
                fn key_bytes(&self) -> &[u8] {
                    self.as_slice().key_bytes()
                }
            }
        )+
    }
}

// Primitives
impl_unsafe_transform!(
    bool, char, f32, f64, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
);
