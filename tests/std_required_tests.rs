//! Tests that require access to the standard library,
//! e.g. for catching panics

use fixed_slice_vec::{FixedSliceVec, IndexError, StorageError};
use proptest::std_facade::HashMap;
use std::mem::MaybeUninit;
use std::panic::AssertUnwindSafe;

fn uninit_storage() -> [MaybeUninit<u8>; 4] {
    [MaybeUninit::new(0u8); 4]
}

#[test]
fn manual_remove() {
    let expected = [0u8, 2, 4, 8];
    let mut storage = uninit_storage();
    let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());

    assert_eq!(2, fsv.remove(1));
    assert_eq!(&[0u8, 4, 8], fsv.as_slice());

    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(100)));
    assert!(unwind.is_err());
}

#[test]
fn manual_push() {
    let mut storage = [MaybeUninit::new(0u8); 16];
    let mut fsv: FixedSliceVec<u32> = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    fsv.push(314);
    assert_eq!(&[314u32], fsv.as_slice());

    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| {
        for i in 0..16 {
            fsv.push(i)
        }
    }));
    assert!(unwind.is_err());
}

#[test]
fn manual_try_swap_remove() {
    let expected = [0u8, 2, 4, 8];
    let mut storage = uninit_storage();
    let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());

    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(100)));
    assert!(unwind.is_err());
    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(4)));
    assert!(unwind.is_err());
    assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
    assert_eq!(Ok(2), fsv.try_swap_remove(1));
    assert_eq!(&[0u8, 8, 4], fsv.as_slice());
}

#[test]
fn hashing_successful() {
    let expected = [0u8, 2, 4, 8];
    let mut storage = uninit_storage();
    let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());

    let mut map = HashMap::new();
    map.insert(fsv, "foo");
}

#[test]
fn formatting_successful() {
    let index_error = format!("{:?}", IndexError);
    assert!(index_error.len() > 0);
    let storage_error = format!("{:?}", StorageError("foo"));
    assert!(storage_error.len() > 0);
    assert!(!storage_error.contains("foo"));

    let expected = [0u8, 2, 4, 8];
    let mut storage = uninit_storage();
    let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());
    assert_eq!("[0, 2, 4, 8]", format!("{:?}", fsv))
}
