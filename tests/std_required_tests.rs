//! Tests that require access to the standard library,
//! e.g. for catching panics

use fixed_slice_vec::{FixedSliceVec, IndexError, StorageError};
use proptest::std_facade::HashMap;
use std::mem::MaybeUninit;
use std::panic::AssertUnwindSafe;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn uninit_storage() -> [MaybeUninit<u8>; 4] {
    unsafe { MaybeUninit::uninit().assume_init() }
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
    let mut storage = [MaybeUninit::<u8>::uninit(); 16];
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

struct TrueOnDrop(Arc<AtomicBool>);
impl Drop for TrueOnDrop {
    fn drop(&mut self) {
        self.0.as_ref().store(true, Ordering::SeqCst);
    }
}

#[test]
fn embed_does_not_run_drops_atomic() {
    let flip = Arc::new(AtomicBool::new(false));
    let flip_clone = flip.clone();
    let mut storage: [u8; 16] = [0u8; 16];
    let emb = unsafe {
        fixed_slice_vec::single::embed(&mut storage[..], move |_leftovers| {
            Result::<TrueOnDrop, ()>::Ok(TrueOnDrop(flip_clone))
        })
        .unwrap()
    };

    assert!(!flip.load(Ordering::SeqCst));
    assert!(!emb.0.load(Ordering::SeqCst));

    // Manually clean up the Arc to avoid alloc-related-leak
    unsafe {
        let ptr: *const TrueOnDrop = emb;
        let extracted = ptr.read();
        std::mem::drop(extracted);
    }
}
#[test]
fn embed_uninit_does_not_run_drops_atomic() {
    let flip = Arc::new(AtomicBool::new(false));
    let flip_clone = flip.clone();
    let mut storage: [MaybeUninit<u8>; 16] = unsafe { MaybeUninit::uninit().assume_init() };
    let emb = fixed_slice_vec::single::embed_uninit(&mut storage[..], move |_leftovers| {
        Result::<TrueOnDrop, ()>::Ok(TrueOnDrop(flip_clone))
    })
    .unwrap();

    assert!(!flip.load(Ordering::SeqCst));
    assert!(!emb.0.load(Ordering::SeqCst));

    // Manually clean up the Arc to avoid alloc-related-leak
    unsafe {
        let ptr: *const TrueOnDrop = emb;
        let extracted = ptr.read();
        std::mem::drop(extracted);
    }
}

#[test]
fn fsv_does_not_run_drops_on_push_atomic() {
    let flip = Arc::new(AtomicBool::new(false));
    let mut storage: [MaybeUninit<u8>; 16] = unsafe { MaybeUninit::uninit().assume_init() };
    {
        let mut fsv: FixedSliceVec<TrueOnDrop> = FixedSliceVec::from_uninit_bytes(&mut storage);
        let flip_clone = flip.clone();
        fsv.try_push(TrueOnDrop(flip_clone)).unwrap();
        assert!(!flip.load(Ordering::SeqCst));
    }
    assert!(flip.load(Ordering::SeqCst));
}
