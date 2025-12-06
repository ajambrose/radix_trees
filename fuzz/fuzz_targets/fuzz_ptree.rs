#![no_main]
#![feature(btree_cursors)]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use radix_trees::ptree::KeyMask;
use radix_trees::ptree::PTreeMap;
use std::collections::BTreeMap;
use std::ops::Bound;

const MAX_KEY_LEN: u16 = 4096;

#[derive(Debug)]
struct ArbitraryKey<'a> {
    key_bytes: &'a [u8],
    zero_pad_bytes: usize,
    masklen: u32,
}

impl<'a> ArbitraryKey<'a> {
    fn create_key_mask(&self) -> KeyMask<Vec<u8>> {
        let mut key = vec![0; self.key_bytes.len() + self.zero_pad_bytes];
        key[0..self.key_bytes.len()].copy_from_slice(self.key_bytes);
        KeyMask::new_exact(key, self.masklen).unwrap()
    }
}

impl<'a> Arbitrary<'a> for ArbitraryKey<'a> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let key_len: u16 = u.int_in_range(0..=MAX_KEY_LEN)?;
        let zero_pad_bytes: usize =
            u.int_in_range(0..=MAX_KEY_LEN.checked_sub(key_len).unwrap())? as usize;
        let key_len_bits = key_len as u32 * 8;
        let total_len_bits = key_len_bits + (zero_pad_bytes as u32 * 8);
        let masklen = u.int_in_range(key_len_bits..=total_len_bits)?;
        let key_bytes = u.bytes(key_len as usize)?;
        Ok(Self { key_bytes, zero_pad_bytes, masklen })
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        // 2 bytes for key length + 2 bytes for zero-pad length + 4 bytes for masklen = 8 lower bound
        // 4096 max total key length + 8 bytes = 5004 upper bound
        (8, Some(5004))
    }
}

#[derive(Debug, Arbitrary)]
enum Op<'a> {
    Insert(ArbitraryKey<'a>, u64),
    Remove(ArbitraryKey<'a>),
    Get(ArbitraryKey<'a>),
    GetBest(ArbitraryKey<'a>),
    Suffixes(ArbitraryKey<'a>, bool),
}

fuzz_target!(|ops: Vec<Op>| {
    let mut tree = PTreeMap::new();
    let mut expected = BTreeMap::new();

    for op in ops {
        match op {
            Op::Insert(key, val) => {
                let km = key.create_key_mask();
                assert_eq!(expected.insert(km.clone(), val), tree.insert_exact(km, val));
            }
            Op::Remove(key) => {
                let km = key.create_key_mask();
                assert_eq!(expected.remove(&km), tree.remove_exact(km).map(|t| t.1));
            }
            Op::Get(key) => {
                let km = key.create_key_mask();
                assert_eq!(expected.get(&km), tree.get_exact(km));
            }
            Op::GetBest(key) => {
                let km = key.create_key_mask();
                let best_km = match tree.get_best_masklen(km.as_ref()) {
                    Some((best_km, best_v)) => {
                        let best_km = KeyMask::clone_borrowed(&best_km);
                        assert_eq!(expected.get(&best_km).unwrap(), best_v);
                        best_km
                    }
                    None => KeyMask::new(vec![]),
                };

                if best_km == km {
                    continue;
                }

                for (test_km, _) in
                    expected.range((Bound::Excluded(best_km), Bound::Excluded(km.clone())))
                {
                    assert!(!test_km.is_prefix_of(&km.as_ref()));
                }
            }
            Op::Suffixes(key, include_exact) => {
                let start_km = key.create_key_mask();
                let op = if include_exact { Bound::Included } else { Bound::Excluded };
                let mut start = expected.lower_bound(op(&start_km));
                let btree_iter = std::iter::from_fn(|| {
                    start.next().map(|(k, v)| (k.as_ref(), v)).and_then(|(km, v)| {
                        if start_km.masklen() <= km.masklen()
                            && start_km.branch_masklen(&km) >= start_km.masklen()
                        {
                            Some((km, v))
                        } else {
                            None
                        }
                    })
                });
                assert!(
                    tree.iter_suffixes_masklen(start_km.as_ref(), include_exact).eq(btree_iter)
                );
            }
        };
    }

    assert_eq!(tree.len(), expected.len());
    assert!(tree.iter().eq(expected.iter().map(|(km, val)| (km.as_ref(), val))));
});
