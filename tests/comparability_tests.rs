use arrayvec::ArrayVec;
use fixed_slice_vec::*;
use std::mem::MaybeUninit;
use std::panic::AssertUnwindSafe;
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

    fn try_insert(&mut self, index: usize, item: Self::Item) -> Result<(), ()>;
    fn insert(&mut self, index: usize, item: Self::Item) {
        self.try_insert(index, item).unwrap()
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
    fn truncate(&mut self, len: usize);
    fn try_remove(&mut self, index: usize) -> Result<Self::Item, ()>;
    fn try_swap_remove(&mut self, index: usize) -> Result<Self::Item, ()>;
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

    fn try_insert(&mut self, index: usize, item: Self::Item) -> Result<(), ()> {
        Vec::insert(self, index, item);
        Ok(())
    }

    fn insert(&mut self, index: usize, item: Self::Item) {
        Vec::insert(self, index, item)
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

    fn truncate(&mut self, len: usize) {
        Vec::truncate(self, len)
    }

    fn try_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        std::panic::catch_unwind(AssertUnwindSafe(|| Vec::remove(self, index))).map_err(|_| ())
    }

    fn try_swap_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        std::panic::catch_unwind(AssertUnwindSafe(|| Vec::swap_remove(self, index))).map_err(|_| ())
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

    fn try_insert(&mut self, index: usize, item: Self::Item) -> Result<(), ()> {
        Vec::insert(self, index, item);
        Ok(())
    }

    fn insert(&mut self, index: usize, item: Self::Item) {
        Vec::insert(self, index, item)
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

    fn truncate(&mut self, len: usize) {
        Vec::truncate(self, len)
    }

    fn try_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        std::panic::catch_unwind(AssertUnwindSafe(|| Vec::remove(self, index))).map_err(|_| ())
    }

    fn try_swap_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        std::panic::catch_unwind(AssertUnwindSafe(|| Vec::swap_remove(self, index))).map_err(|_| ())
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

    fn try_insert(&mut self, index: usize, item: Self::Item) -> Result<(), ()> {
        self.try_insert(index, item).map_err(|_| ())
    }
    fn insert(&mut self, index: usize, item: Self::Item) {
        self.insert(index, item)
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

    fn truncate(&mut self, len: usize) {
        FixedSliceVec::truncate(self, len)
    }

    fn try_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        FixedSliceVec::try_remove(self, index).map_err(|_| ())
    }

    fn try_swap_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        FixedSliceVec::try_swap_remove(self, index).map_err(|_| ())
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

    fn try_insert(&mut self, index: usize, item: Self::Item) -> Result<(), ()> {
        ArrayVec::try_insert(self, index, item).map_err(|_| ())
    }

    fn insert(&mut self, index: usize, item: Self::Item) {
        ArrayVec::insert(self, index, item)
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

    fn truncate(&mut self, len: usize) {
        ArrayVec::truncate(self, len)
    }

    fn try_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        ArrayVec::pop_at(self, index).ok_or_else(|| ())
    }

    fn try_swap_remove(&mut self, index: usize) -> Result<Self::Item, ()> {
        ArrayVec::swap_pop(self, index).ok_or_else(|| ())
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

#[test]
fn drops_items_when_truncate() {
    assert_vec_like_drops_items_when_truncate(Vec::new());

    let mut backing: [MaybeUninit<DropCountingItem>; 10] =
        unsafe { MaybeUninit::uninit().assume_init() };
    let sv: FixedSliceVec<_> = FixedSliceVec::new(&mut backing[..]);
    assert_eq!(10, VecLike::capacity(&sv));
    assert_eq!(0, sv.len());
    assert_vec_like_drops_items_when_truncate(sv);
}

fn assert_vec_like_drops_items_when_truncate<V: VecLike<Item = DropCountingItem>>(v: V) {
    let count = Arc::new(AtomicUsize::new(0));
    let item_a = DropCountingItem {
        drop_count: count.clone(),
    };
    let item_b = DropCountingItem {
        drop_count: count.clone(),
    };
    {
        let mut v = v;
        v.push(item_a);
        v.push(item_b);
        assert_eq!(0, count.load(Ordering::SeqCst));
        v.truncate(1);
        assert_eq!(1, count.load(Ordering::SeqCst));
    }
    assert_eq!(2, count.load(Ordering::SeqCst));
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
    pub enum VecLikeOp<I, T> {
        Push(T),
        Insert(I, T),
        Pop,
        Clear,
        Truncate(I),
        Remove(I),
        SwapRemove(I),
    }

    fn arbitrary_vec_like_op(
        max_expected_capacity: usize,
    ) -> impl Strategy<Value = VecLikeOp<usize, u16>> {
        // Weighted to avoid clearing so often that we only rarely encounter
        // border conditions
        prop_oneof! [
            30 => any::<(usize, u16)>().prop_map(|(ind, v)| VecLikeOp::Insert(ind, v)),
            20 => any::<u16>().prop_map(|v| VecLikeOp::Push(v)),
            10 => Just(VecLikeOp::Pop),
            4 => (0..(max_expected_capacity*2)).prop_map(|v| VecLikeOp::Remove(v)),
            4 => (0..(max_expected_capacity*2)).prop_map(|v| VecLikeOp::SwapRemove(v)),
            4 => (0..(max_expected_capacity*2)).prop_map(|v| VecLikeOp::Truncate(v)),
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
        operations: Vec<VecLikeOp<usize, u16>>,
        mut storage_bytes: Vec<MaybeUninit<u8>>,
    ) -> Result<(), TestCaseError> {
        let mut fs_vec: FixedSliceVec<u16> = FixedSliceVec::from_uninit_bytes(&mut storage_bytes);
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
                VecLikeOp::Insert(i, v) => {
                    let fs_result = fs_vec.try_insert(i, v);
                    if let Err(e) = fs_result {
                        let insert_failure_expected =
                            (other_vec.capacity() == other_vec.len()) || (i > other_vec.len());
                        prop_assert!(insert_failure_expected, "FixedSliceVec should only reject when full or insertion index outside valid range. Failed inserting {:?} at {:?}", e, i);
                    } else {
                        if let Err(e) = other_vec.try_insert(i, v) {
                            let insert_failure_expected =
                                (other_vec.capacity() == other_vec.len()) || (i > other_vec.len());
                            prop_assert!(insert_failure_expected, "Other VecLike implementations should only reject when full or insertion index outside valid range. Failed inserting {:?} at {:?}", e, i);
                            // Roll back the value just added so we don't diverge simply because
                            // of different capacities.
                            assert_eq!(
                                Ok(v),
                                fs_vec.try_remove(i),
                                "Ought to have popped back what we just inserted"
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
                    let other_result = other_vec.pop();
                    prop_assert_eq!(
                        other_result,
                        fs_result,
                        "Returned values from `pop` should be the same"
                    );
                }
                VecLikeOp::Truncate(truncate_len) => {
                    let prior_fs_length = fs_vec.len();
                    let prior_other_length = other_vec.len();
                    prop_assert_eq!(
                        prior_fs_length,
                        prior_other_length,
                        "The 2 vecs had out-of-sync starting lengths"
                    );
                    fs_vec.truncate(truncate_len);
                    other_vec.truncate(truncate_len);
                    let posterior_fs_length = fs_vec.len();
                    let posterior_other_length = other_vec.len();
                    if truncate_len <= prior_fs_length {
                        prop_assert_eq!(
                            posterior_fs_length,
                            truncate_len,
                            "fsv did not truncate to the target len"
                        );
                        prop_assert_eq!(
                            posterior_other_length,
                            truncate_len,
                            "other did not truncate to the target len"
                        );
                    }
                }
                VecLikeOp::Remove(index) => {
                    let fs_result = VecLike::try_remove(&mut fs_vec, index);
                    let other_result = VecLike::try_remove(other_vec, index);
                    prop_assert_eq!(
                        other_result,
                        fs_result,
                        "Returned values from `try_remove` should be the same"
                    );
                }
                VecLikeOp::SwapRemove(index) => {
                    let fs_result = VecLike::try_swap_remove(&mut fs_vec, index);
                    let other_result = VecLike::try_swap_remove(other_vec, index);
                    prop_assert_eq!(
                        other_result,
                        fs_result,
                        "Returned values from `try_swap_remove` should be the same"
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
            operations in proptest::collection::vec(arbitrary_vec_like_op(512), 1..1000),
            storage_bytes in proptest::collection::vec(Just(MaybeUninit::new(0u8)), 0..1024)
        ) {
            let mut std_vec = Vec::new();
            assert_alike_operations(&mut std_vec, operations, storage_bytes)?;
        }
        #[test]
        #[cfg_attr(miri, ignore)]
        fn compare_vec_like_operations_against_array_vec(
            operations in proptest::collection::vec(arbitrary_vec_like_op(512), 1..1000),
            storage_bytes in proptest::collection::vec(Just(MaybeUninit::new(0u8)), 0..1024)
        ) {
            let mut av_vec: ArrayVec<[u16; 32]> = ArrayVec::new();
            assert_alike_operations(&mut av_vec, operations, storage_bytes)?;
        }
    }
}
