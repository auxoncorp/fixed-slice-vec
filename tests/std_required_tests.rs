//! Tests that require access to the standard library,
//! e.g. for catching panics

use fixed_slice_vec::{FixedSliceVec, IndexError, StorageError};
use proptest::std_facade::HashMap;
use std::mem::MaybeUninit;
use std::panic::AssertUnwindSafe;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

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
    let mut storage: [MaybeUninit<u8>; 16] = unsafe { MaybeUninit::uninit().assume_init() };
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

struct PanicDropHelper {
    drop_counter: Arc<Mutex<usize>>,
    panic_on_drop: Arc<Mutex<bool>>,
}
impl Drop for PanicDropHelper {
    fn drop(&mut self) {
        if let Ok(mut drop_counter) = self.drop_counter.lock() {
            *drop_counter = drop_counter.saturating_add(1);
        }
        let should_panic = if let Ok(panic_on_drop) = self.panic_on_drop.lock() {
            *panic_on_drop
        } else {
            false
        };
        if should_panic {
            panic!("As you wish");
        }
    }
}

#[test]
fn double_drop_averted_despite_panic_during_clear() {
    // Detect the case when a panic in the middle of a `clear` call
    // may leave the FSV in an uncertain state which may cause double-frees
    // during subsequent calls to `clear`
    let drop_counters = vec![
        Arc::new(Mutex::new(0)),
        Arc::new(Mutex::new(0)),
        Arc::new(Mutex::new(0)),
    ];
    let panic_on_drop_instructions = vec![
        Arc::new(Mutex::new(false)),
        Arc::new(Mutex::new(true)),
        Arc::new(Mutex::new(false)),
    ];
    let mut storage: [MaybeUninit<u8>; 1024] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut fsv: FixedSliceVec<PanicDropHelper> = FixedSliceVec::from_uninit_bytes(&mut storage);
    for (drop_counter, panic_on_drop) in drop_counters.iter().zip(panic_on_drop_instructions.iter())
    {
        fsv.push(PanicDropHelper {
            drop_counter: drop_counter.clone(),
            panic_on_drop: panic_on_drop.clone(),
        });
    }
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        fsv.clear();
    }));
    assert!(r.is_err());

    let found_n_drops: Vec<usize> = drop_counters.iter().map(|dc| *dc.lock().unwrap()).collect();
    assert!(found_n_drops.iter().sum::<usize>() <= 3);

    assert!(fsv.is_empty());

    for panic_on_drop in panic_on_drop_instructions {
        let mut pod = panic_on_drop.lock().unwrap();
        *pod = false;
    }

    fsv.clear();
    assert!(found_n_drops.iter().sum::<usize>() <= 3);

    assert!(fsv.is_empty());
}
#[test]
fn double_drop_averted_despite_panic_during_truncate() {
    // Detect the case when a panic in the middle of a `truncate` call
    // may leave the FSV in an uncertain state which may cause double-frees
    // during subsequent calls to `truncate`
    let drop_counters = vec![
        Arc::new(Mutex::new(0)),
        Arc::new(Mutex::new(0)),
        Arc::new(Mutex::new(0)),
    ];
    let panic_on_drop_instructions = vec![
        Arc::new(Mutex::new(false)),
        Arc::new(Mutex::new(true)),
        Arc::new(Mutex::new(false)),
    ];
    let mut storage: [MaybeUninit<u8>; 1024] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut fsv: FixedSliceVec<PanicDropHelper> = FixedSliceVec::from_uninit_bytes(&mut storage);
    for (drop_counter, panic_on_drop) in drop_counters.iter().zip(panic_on_drop_instructions.iter())
    {
        fsv.push(PanicDropHelper {
            drop_counter: drop_counter.clone(),
            panic_on_drop: panic_on_drop.clone(),
        });
    }
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        fsv.truncate(1);
    }));
    assert!(r.is_err());

    let found_n_drops: Vec<usize> = drop_counters.iter().map(|dc| *dc.lock().unwrap()).collect();
    assert!(found_n_drops.iter().sum::<usize>() <= 2);

    assert_eq!(1, fsv.len());

    for panic_on_drop in panic_on_drop_instructions {
        let mut pod = panic_on_drop.lock().unwrap();
        *pod = false;
    }

    fsv.truncate(1);
    assert!(found_n_drops.iter().sum::<usize>() <= 2);
    assert_eq!(1, fsv.len());

    fsv.truncate(0);
    assert!(fsv.is_empty());
    assert!(found_n_drops.iter().sum::<usize>() <= 3);
}
