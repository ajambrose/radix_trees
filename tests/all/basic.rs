use radix_trees::ptree::{KeyMask, PTreeMap};
use zerocopy::byteorder::big_endian::U32;
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
fn default_iter() {
    let t = PTreeMap::<u32, u32>::default();
    let i = t.iter();
    assert_eq!(i.count(), 0);

    let i = (&t).into_iter();
    assert_eq!(i.count(), 0);
}

#[test]
fn insert_one() {
    let mut t = PTreeMap::<u32, u32>::default();
    assert_eq!(t.insert(1, 2), None);
    assert_eq!(t.len(), 1);
    assert_eq!(t.get_exact(KeyMask::new_exact(1, 32).unwrap()).copied(), Some(2));
    assert_eq!(t.get_exact(KeyMask::new_exact(2, 32).unwrap()).copied(), None);
}

#[test]
fn insert_two_lr() {
    let mut t = PTreeMap::<u32, u32>::default();
    assert_eq!(t.insert(2, 4), None);
    assert_eq!(t.insert(3, 6), None);
    assert_eq!(t.len(), 2);
    assert_eq!(t.get_exact(KeyMask::new_exact(2, 32).unwrap()).copied(), Some(4));
    assert_eq!(t.get_exact(KeyMask::new_exact(3, 32).unwrap()).copied(), Some(6));
}

#[test]
fn insert_two_rl() {
    let mut t = PTreeMap::<u32, u32>::default();
    assert_eq!(t.insert(3, 4), None);
    assert_eq!(t.insert(2, 6), None);
    assert_eq!(t.len(), 2);
    assert_eq!(t.get_exact(KeyMask::new_exact(2, 32).unwrap()).copied(), Some(6));
    assert_eq!(t.get_exact(KeyMask::new_exact(3, 32).unwrap()).copied(), Some(4));
}

#[test]
fn branch_to_val() {
    let a = U32::new(2);
    let b = U32::new(3);
    let mut t = PTreeMap::<U32, u32>::default();
    assert_eq!(t.insert_exact(KeyMask::new_exact(a, 32).unwrap(), 4), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(b, 32).unwrap(), 6), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(a, 31).unwrap(), 8), None);
    assert_eq!(t.len(), 3);
    assert_eq!(t.get_exact(KeyMask::new_exact(&a, 32).unwrap()).copied(), Some(4));
    assert_eq!(t.get_exact(KeyMask::new_exact(&b, 32).unwrap()).copied(), Some(6));
    assert_eq!(t.get_exact(KeyMask::new_exact(&a, 31).unwrap()).copied(), Some(8));
}

#[test]
fn insert_inline() {
    let a = U32::new(0x00000000);
    let ap = U32::new(0x00000000);
    let b = U32::new(0x01000001);
    let bp = U32::new(0x01000000);
    let mut t = PTreeMap::<U32, u32>::default();

    assert_eq!(t.insert_exact(KeyMask::new_exact(a, 32).unwrap(), 0), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(b, 32).unwrap(), 1), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(ap, 31).unwrap(), 2), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(bp, 31).unwrap(), 3), None);
    assert_eq!(t.len(), 4);
    assert_eq!(t.get_exact(KeyMask::new_exact(&a, 32).unwrap()).copied(), Some(0));
    assert_eq!(t.get_exact(KeyMask::new_exact(&b, 32).unwrap()).copied(), Some(1));
    assert_eq!(t.get_exact(KeyMask::new_exact(&ap, 31).unwrap()).copied(), Some(2));
    assert_eq!(t.get_exact(KeyMask::new_exact(&bp, 31).unwrap()).copied(), Some(3));
}

#[test]
fn branch_backtrack() {
    let keys = [(0xff000000, 8), (0xff000000, 16), (0xff000000, 24), (0xff000000, 32)]
        .map(|(k, m)| KeyMask::new_exact(U32::new(k), m).unwrap());
    let vals = [0u32, 1, 2, 3];
    let mut expected: Vec<_> = keys.iter().cloned().zip(vals).collect();
    let mut t: PTreeMap<_, _> = expected.iter().cloned().collect();
    // reaches 255/32 then backtracks
    let km1 = KeyMask::new_exact(U32::new(0xff001100), 32).unwrap();
    // takes empty right branch from 255/24 then backtracks
    let km2 = KeyMask::new_exact(U32::new(0xff010080), 32).unwrap();
    expected.push((km1, 5));
    expected.push((km2, 6));
    assert_eq!(t.insert_exact(km1, 5), None);
    assert_eq!(t.insert_exact(km2, 6), None);
    assert_eq!(t.into_iter().collect::<Vec<_>>(), expected);
}

#[test]
fn remove() {
    let a = U32::new(0x00000000);
    let ap = U32::new(0x00000000);
    let b = U32::new(0x01000001);
    let bp = U32::new(0x01000000);
    let mut t = PTreeMap::<U32, u32>::default();

    assert_eq!(t.insert_exact(KeyMask::new_exact(a, 32).unwrap(), 0), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(b, 32).unwrap(), 1), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(ap, 31).unwrap(), 2), None);
    assert_eq!(t.insert_exact(KeyMask::new_exact(bp, 31).unwrap(), 3), None);

    assert_eq!(t.len(), 4);
    assert_eq!(t.get_exact(KeyMask::new_exact(&ap, 31).unwrap()).copied(), Some(2));
    let km = KeyMask::new_exact(&ap, 31).unwrap();
    assert_eq!(t.remove_exact(km), Some((KeyMask::clone_borrowed(&km), 2u32)));
    assert_eq!(t.get_exact(KeyMask::new_exact(&ap, 31).unwrap()), None);
}

#[test]
fn trie_iter() {
    let keys = [(0, 31), (0, 32), (0x01000000, 31), (0x01000001, 32)]
        .map(|(k, m)| KeyMask::new_exact(U32::new(k), m).unwrap());
    let vals = [0u32, 1, 2, 3];
    let expected: Vec<_> = keys.iter().cloned().zip(vals).collect();

    let t: PTreeMap<_, _> = expected.iter().cloned().collect();
    assert_eq!(t.len(), 4);
    assert_eq!(t.iter().cloned().collect::<Vec<_>>(), expected);
    assert_eq!(t.into_iter().collect::<Vec<_>>(), expected);
}

#[test]
fn trie_iter_mut() {
    let keys = [(0, 31), (0, 32), (0x01000000, 31), (0x01000001, 32)]
        .map(|(k, m)| KeyMask::new_exact(U32::new(k), m).unwrap());
    let vals = [0u32, 1, 2, 3];
    let mut expected: Vec<_> = keys.iter().cloned().zip(vals).collect();

    let mut t: PTreeMap<_, _> = expected.iter().cloned().collect();
    expected.iter_mut().for_each(|(_, n)| *n *= 2);
    assert_eq!(t.len(), 4);

    // collect references in a Vec to make sure they are long-lived,
    // to ensure Miri has an opportunity to catch any potential borrow aliases
    let v: Vec<_> = t.iter_mut().collect();
    v.into_iter().for_each(|(_, n)| *n *= 2);
    assert_eq!(t.iter().copied().collect::<Vec<_>>(), expected);
    assert_eq!(t.into_iter().collect::<Vec<_>>(), expected);
}

#[test]
fn strings() {
    let keys = ["Hello", "Hello world!", "Ferris", "Ferris Bueller"]
        .map(|s| KeyMask::new(std::string::String::from(s)));
    let vals = [0u32, 1, 2, 3];
    let mut expected: Vec<_> = keys.iter().cloned().zip(vals).collect();
    let t: PTreeMap<_, _> = expected.iter().cloned().collect();
    expected.sort_by(|(km1, _), (km2, _)| km1.cmp(km2));
    assert_eq!(t.iter().cloned().collect::<Vec<_>>(), expected);
    assert_eq!(t.into_iter().collect::<Vec<_>>(), expected);
}

#[test]
fn get_best() {
    let keys = ["sugar", "suggest", "super", "suggestion", "superhero", "suggests", "sugars"];
    let vals = 0..8;

    let mut t: PTreeMap<_, _> = keys.into_iter().zip(vals).collect();

    assert_eq!(t.get_best("suggester").unwrap().0, KeyMask::new(&"suggest"));
    assert_eq!(t.get_best("superheroes").unwrap().0, KeyMask::new(&"superhero"));
    assert_eq!(t.get_best("sucralose"), None);

    t.insert("", 8);

    assert_eq!(t.get_best("sucralose").unwrap().0, KeyMask::new(&""));
}

#[test]
fn iter_suffixes() {
    let keys = ["sugar", "suggest", "super", "suggestion", "superhero", "suggests", "sugars", ""];
    let vals = 0..8;

    let t: PTreeMap<_, _> = keys.into_iter().zip(vals).collect();

    let v: Vec<_> = t.iter_suffixes("sug", false).map(|(km, _)| **km.key()).collect();
    assert_eq!(v, ["sugar", "sugars", "suggest", "suggestion", "suggests"]);
    let v: Vec<_> = t.iter_suffixes("suggest", false).map(|(km, _)| **km.key()).collect();
    assert_eq!(v, ["suggestion", "suggests"]);
    let v: Vec<_> = t.iter_suffixes("super", true).map(|(km, _)| **km.key()).collect();
    assert_eq!(v, ["super", "superhero"]);
    let v: Vec<_> = t.iter_suffixes("", false).map(|(km, _)| **km.key()).collect();
    assert_eq!(v, ["sugar", "sugars", "suggest", "suggestion", "suggests", "super", "superhero"]);

    assert_eq!(t.iter_suffixes("sucralose", true).collect::<Vec<_>>(), vec![]);
    assert_eq!(t.iter_suffixes("superhero", false).collect::<Vec<_>>(), vec![]);
    assert_eq!(t.iter_suffixes("suggestions", true).collect::<Vec<_>>(), vec![]);
}
