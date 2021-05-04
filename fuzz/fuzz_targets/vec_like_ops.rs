#![no_main]
extern crate fixed_slice_vec;
extern crate libfuzzer_sys;
use fixed_slice_vec::FixedSliceVec;
use libfuzzer_sys::{arbitrary, fuzz_target};

#[derive(Debug, Clone, arbitrary::Arbitrary)]
pub struct Harness {
    storage: Vec<u8>,
    ops: Vec<VecLikeOp<String>>,
}
#[derive(Debug, Clone, arbitrary::Arbitrary)]
pub enum VecLikeOp<T> {
    Push(T),
    Pop,
    Clear,
    Truncate(usize),
    Remove(usize),
    SwapRemove(usize),
    Extend(Vec<T>),
}

fuzz_target!(|harness: Harness| {
    let Harness { mut storage, ops } = harness;
    let mut fsv: FixedSliceVec<String> = unsafe { FixedSliceVec::from_bytes(&mut storage[..]) };
    for op in ops {
        match op {
            VecLikeOp::Clear => {
                fsv.clear();
            }
            VecLikeOp::Pop => {
                let _ = fsv.pop();
            }
            VecLikeOp::Push(s) => {
                let _ = fsv.try_push(s);
            }
            VecLikeOp::Remove(index) => {
                let _ = fsv.try_remove(index);
            }
            VecLikeOp::SwapRemove(index) => {
                let _ = fsv.try_swap_remove(index);
            }
            VecLikeOp::Truncate(len) => {
                let _ = fsv.truncate(len);
            }
            VecLikeOp::Extend(other) => {
                let _ = fsv.try_extend(other.into_iter());
            }
        }
    }
});
