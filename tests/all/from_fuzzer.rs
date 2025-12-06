//! Tests derived from failed fuzzer runs.

use radix_trees::ptree::{KeyMask, PTreeMap};
extern crate std;

#[test]
fn insert_twice() {
    let mut t = PTreeMap::new();
    assert!(t.insert(1, 1).is_none());
    assert_eq!(t.insert(1, 2), Some(1));
}

#[test]
fn insert_masked_twice() {
    let mut t = PTreeMap::new();
    assert!(t.insert_exact(KeyMask::new_exact(0u64, 17).unwrap(), 1).is_none());
    assert_eq!(t.insert_exact(KeyMask::new_exact(0u64, 17).unwrap(), 2), Some(1));
}

#[test]
fn branch_merge_root() {
    let keys = [vec![0u8; 0], vec![0; 1], vec![0; 2]];
    let masks = [0, 6, 12];
    let vals = 0..3;

    let mut expected: Vec<_> = keys
        .into_iter()
        .zip(masks)
        .map(|(k, m)| KeyMask::new_exact(k, m).unwrap())
        .zip(vals)
        .collect();

    let mut t: PTreeMap<_, _> = expected.iter().cloned().collect();

    expected.remove(0);
    t.remove(vec![]);
    assert_eq!(expected, t.into_iter().collect::<Vec<_>>());
}

#[test]
fn remove_root() {
    let keys = [vec![167u8, 167, 167, 16], vec![0; 64], vec![0; 64], vec![0; 41], vec![]];
    let masks = [32, 254, 255, 253, 0];
    let vals = 0..5;

    let mut expected: Vec<_> = keys
        .into_iter()
        .zip(masks)
        .map(|(k, m)| KeyMask::new_exact(k, m).unwrap())
        .zip(vals)
        .collect();

    let mut t: PTreeMap<_, _> = expected.iter().cloned().collect();

    expected.sort();
    expected.remove(0);
    t.remove(vec![]);
    assert_eq!(expected, t.into_iter().collect::<Vec<_>>());
}

#[test]
fn remove_leaf() {
    let keys = [vec![0u8, 185], vec![255, 28]];
    let masks = [16, 16];
    let vals = 0..2;

    let mut expected: Vec<_> = keys
        .into_iter()
        .zip(masks)
        .map(|(k, m)| KeyMask::new_exact(k, m).unwrap())
        .zip(vals)
        .collect();

    let mut t: PTreeMap<_, _> = expected.iter().cloned().collect();

    expected.pop();
    t.remove(vec![255, 28]);
    assert_eq!(expected, t.into_iter().collect::<Vec<_>>());
}

#[test]
fn get_best_prefix_none() {
    let keys = [vec![0u8; 8]];
    let masks = [32];
    let vals = 0..1;
    let t: PTreeMap<_, _> = keys
        .into_iter()
        .zip(masks)
        .map(|(k, m)| KeyMask::new_exact(k, m).unwrap())
        .zip(vals)
        .collect();
    assert!(t.get_best_masklen(KeyMask::new_exact(vec![0u8; 4], 16).unwrap()).is_none());
}
