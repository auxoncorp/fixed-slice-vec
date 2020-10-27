//! Tests that require access to the standard library,
//! e.g. for catching panics

use fixed_slice_vec::FixedSliceVec;
use std::panic::AssertUnwindSafe;

#[test]
fn manual_remove() {
    let expected = [0u8, 2, 4, 8];
    let mut storage = [0u8; 4];
    let mut fsv = FixedSliceVec::from_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());

    assert_eq!(2, fsv.remove(1));
    assert_eq!(&[0u8, 4, 8], fsv.as_slice());

    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(100)));
    assert!(unwind.is_err());
}

#[test]
fn manual_push() {
    let mut storage = [0u8; 16];
    let mut fsv: FixedSliceVec<u32> = FixedSliceVec::from_bytes(&mut storage[..]);
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
    let mut storage = [0u8; 4];
    let mut fsv = FixedSliceVec::from_bytes(&mut storage[..]);
    assert!(fsv.try_extend(expected.iter().copied()).is_ok());

    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(100)));
    assert!(unwind.is_err());
    let unwind = std::panic::catch_unwind(AssertUnwindSafe(|| fsv.remove(4)));
    assert!(unwind.is_err());
    assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
    assert_eq!(Ok(2), fsv.try_swap_remove(1));
    assert_eq!(&[0u8, 8, 4], fsv.as_slice());
}
