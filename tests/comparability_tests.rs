use arrayvec::ArrayVec;
use fixed_slice_vec::*;
use std::mem::MaybeUninit;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[derive(Clone)]
struct DropCountingItem {
    drop_count: Arc<AtomicUsize>,
}

impl Drop for DropCountingItem {
    fn drop(&mut self) {
        self.drop_count.fetch_add(1, Ordering::SeqCst);
    }
}

trait VecLike {
    type Item: Sized;
    fn try_push(&mut self, item: Self::Item) -> Result<(), ()>;
    fn push(&mut self, item: Self::Item) {
        self.try_push(item).unwrap()
    }

    fn pop(&mut self) -> Option<Self::Item>;
    fn clear(&mut self);
    fn capacity(&self) -> usize;
    fn as_slice(&self) -> &[Self::Item];
    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn len(&self) -> usize {
        self.as_slice().len()
    }
}

impl<T> VecLike for Vec<T> {
    type Item = T;

    fn try_push(&mut self, item: Self::Item) -> Result<(), ()> {
        Vec::push(self, item);
        Ok(())
    }

    fn push(&mut self, item: Self::Item) {
        Vec::push(self, item)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(self)
    }

    fn clear(&mut self) {
        Vec::clear(self)
    }

    fn capacity(&self) -> usize {
        Vec::capacity(self)
    }

    fn as_slice(&self) -> &[Self::Item] {
        self
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    fn is_empty(&self) -> bool {
        Vec::is_empty(self)
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }
}

impl<'a, T> VecLike for &'a mut Vec<T> {
    type Item = T;

    fn try_push(&mut self, item: Self::Item) -> Result<(), ()> {
        Vec::push(self, item);
        Ok(())
    }

    fn push(&mut self, item: Self::Item) {
        Vec::push(self, item)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(self)
    }

    fn clear(&mut self) {
        Vec::clear(self)
    }

    fn capacity(&self) -> usize {
        Vec::capacity(self)
    }

    fn as_slice(&self) -> &[Self::Item] {
        self
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    fn is_empty(&self) -> bool {
        Vec::is_empty(self)
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }
}

impl<'a, T> VecLike for FixedSliceVec<'a, T> {
    type Item = T;

    fn try_push(&mut self, item: Self::Item) -> Result<(), ()> {
        self.try_push(item).map_err(|_| ())
    }
    fn push(&mut self, item: Self::Item) {
        self.push(item);
    }

    fn pop(&mut self) -> Option<Self::Item> {
        self.pop()
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn as_slice(&self) -> &[Self::Item] {
        self
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }
}

impl<'a, T> VecLike for ArrayVec<[T; 32]> {
    type Item = T;

    fn try_push(&mut self, item: Self::Item) -> Result<(), ()> {
        ArrayVec::try_push(self, item).map_err(|_| ())
    }

    fn push(&mut self, item: Self::Item) {
        ArrayVec::push(self, item)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        ArrayVec::pop(self)
    }

    fn clear(&mut self) {
        ArrayVec::clear(self)
    }

    fn capacity(&self) -> usize {
        ArrayVec::capacity(self)
    }

    fn as_slice(&self) -> &[Self::Item] {
        ArrayVec::as_slice(self)
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        ArrayVec::as_mut_slice(self)
    }

    fn is_empty(&self) -> bool {
        ArrayVec::len(self) == 0
    }

    fn len(&self) -> usize {
        ArrayVec::len(self)
    }
}

fn assert_vec_like_drops_items_when_dropped<V: VecLike<Item = DropCountingItem>>(v: V) {
    let count = Arc::new(AtomicUsize::new(0));
    {
        let mut v = v;
        v.push(DropCountingItem {
            drop_count: count.clone(),
        });
        assert_eq!(0, count.load(Ordering::SeqCst));
    }
    assert_eq!(1, count.load(Ordering::SeqCst));
}

#[test]
fn drops_items_when_dropped() {
    assert_vec_like_drops_items_when_dropped(Vec::new());

    let mut backing: [MaybeUninit<DropCountingItem>; 10] =
        unsafe { MaybeUninit::uninit().assume_init() };
    let sv: FixedSliceVec<_> = FixedSliceVec::new(&mut backing[..]);
    assert_eq!(10, VecLike::capacity(&sv));
    assert_eq!(0, sv.len());
    assert_vec_like_drops_items_when_dropped(sv);
}

fn assert_vec_like_drops_items_when_clear<V: VecLike<Item = DropCountingItem>>(v: V) {
    let count = Arc::new(AtomicUsize::new(0));
    let item = DropCountingItem {
        drop_count: count.clone(),
    };
    {
        let mut v = v;
        v.push(item);
        assert_eq!(0, count.load(Ordering::SeqCst));
        v.clear();
        assert_eq!(1, count.load(Ordering::SeqCst));
    }
    assert_eq!(1, count.load(Ordering::SeqCst));
}

#[test]
fn drops_items_when_clear() {
    assert_vec_like_drops_items_when_clear(Vec::new());

    let mut backing: [MaybeUninit<DropCountingItem>; 10] =
        unsafe { MaybeUninit::uninit().assume_init() };
    let sv: FixedSliceVec<_> = FixedSliceVec::new(&mut backing[..]);
    assert_vec_like_drops_items_when_clear(sv);
}

fn assert_vec_like_drops_items_replaced_via_mut_slice<V: VecLike<Item = DropCountingItem>>(v: V) {
    let count_a = Arc::new(AtomicUsize::new(0));
    let count_b = Arc::new(AtomicUsize::new(0));
    {
        let mut v = v;
        v.push(DropCountingItem {
            drop_count: count_a.clone(),
        });
        assert_eq!(0, count_a.load(Ordering::SeqCst));
        let v_ref: &mut [DropCountingItem] = v.as_mut_slice();
        assert_eq!(0, count_a.load(Ordering::SeqCst));
        v_ref[0] = DropCountingItem {
            drop_count: count_b.clone(),
        };
        assert_eq!(1, count_a.load(Ordering::SeqCst));
        assert_eq!(0, count_b.load(Ordering::SeqCst));
        {
            let _item_b = v.pop();
            assert_eq!(0, count_b.load(Ordering::SeqCst));
        }
        assert_eq!(1, count_b.load(Ordering::SeqCst));
    }
    assert_eq!(1, count_a.load(Ordering::SeqCst));
    assert_eq!(1, count_b.load(Ordering::SeqCst));
}

#[test]
fn drops_items_replaced_via_mut_slice() {
    assert_vec_like_drops_items_replaced_via_mut_slice(Vec::new());

    let mut backing: [MaybeUninit<DropCountingItem>; 10] =
        unsafe { MaybeUninit::uninit().assume_init() };
    let sv: FixedSliceVec<_> = FixedSliceVec::new(&mut backing[..]);
    assert_vec_like_drops_items_replaced_via_mut_slice(sv);
}

pub mod vec_like_operations {
    use super::*;
    use proptest::prelude::*;
    #[derive(Debug, Clone)]
    pub enum VecLikeOp<T> {
        Push(T),
        Pop,
        Clear,
    }

    fn arbitrary_vec_like_op() -> impl Strategy<Value = VecLikeOp<u16>> {
        // Weighted to avoid clearing so often that we only rarely encounter
        // border conditions
        prop_oneof! [
            20 => any::<u16>().prop_map(|v| VecLikeOp::Push(v)),
            15 => Just(VecLikeOp::Pop),
            1 => Just(VecLikeOp::Clear),
        ]
    }

    fn prop_assert_equivalent<'a, T>(
        other_vec: &mut dyn VecLike<Item = T>,
        fixed_slice_vec: &mut FixedSliceVec<'a, T>,
    ) -> Result<(), TestCaseError>
    where
        T: std::fmt::Debug,
        T: PartialEq,
    {
        prop_assert_eq!(
            other_vec.as_slice(),
            fixed_slice_vec.as_slice(),
            "Slice contents"
        );
        prop_assert_eq!(
            other_vec.as_mut_slice(),
            fixed_slice_vec.as_mut_slice(),
            "Mutable slice contents"
        );
        prop_assert_eq!(other_vec.len(), fixed_slice_vec.len(), "Lengths");
        prop_assert_eq!(
            other_vec.is_empty(),
            fixed_slice_vec.is_empty(),
            "Empty statuses"
        );
        Ok(())
    }

    fn assert_alike_operations(
        other_vec: &mut dyn VecLike<Item = u16>,
        operations: Vec<VecLikeOp<u16>>,
        mut storage_bytes: Vec<u8>,
    ) -> Result<(), TestCaseError> {
        let mut fs_vec: FixedSliceVec<u16> = FixedSliceVec::from_bytes(&mut storage_bytes);
        for op in operations {
            match op {
                VecLikeOp::Push(v) => {
                    let fs_result = fs_vec.try_push(v);
                    if let Err(e) = fs_result {
                        prop_assert!(fs_vec.is_full(), "FixedSliceVec should only reject pushes when full. Failed pushing {:?}", e);
                    } else {
                        if let Err(e) = other_vec.try_push(v) {
                            prop_assert_eq!(other_vec.capacity(), other_vec.len(), "Other VecLike implementations should only reject when full. Failed pushing {:?}", e);
                            // Roll back the value just added so we don't diverge simply because
                            // of different capacities.
                            assert_eq!(
                                Some(v),
                                fs_vec.pop(),
                                "Ought to have popped back what we just pushed"
                            );
                        }
                    }
                }
                VecLikeOp::Clear => {
                    fs_vec.clear();
                    other_vec.clear();
                }
                VecLikeOp::Pop => {
                    let fs_result = fs_vec.pop();
                    let std_result = other_vec.pop();
                    prop_assert_eq!(
                        std_result,
                        fs_result,
                        "Returned values from `pop` should be the same"
                    );
                }
            }
            prop_assert_equivalent(other_vec, &mut fs_vec)?;
        }
        Ok(())
    }

    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn compare_vec_like_operations_against_std(
            operations in proptest::collection::vec(arbitrary_vec_like_op(), 1..1000),
            storage_bytes in proptest::collection::vec(Just(0u8), 0..1024)
        ) {
            let mut std_vec = Vec::new();
            assert_alike_operations(&mut std_vec, operations, storage_bytes)?;
        }
        #[test]
        #[cfg_attr(miri, ignore)]
        fn compare_vec_like_operations_against_array_vec(
            operations in proptest::collection::vec(arbitrary_vec_like_op(), 1..1000),
            storage_bytes in proptest::collection::vec(Just(0u8), 0..1024)
        ) {
            let mut av_vec: ArrayVec<[u16; 32]> = ArrayVec::new();
            assert_alike_operations(&mut av_vec, operations, storage_bytes)?;
        }
    }
}
