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
    fn push(&mut self, item: Self::Item);
    fn pop(&mut self) -> Option<Self::Item>;
    fn clear(&mut self);
    fn capacity(&self) -> usize;
    fn as_mut_slice(&mut self) -> &mut [Self::Item];
}

impl VecLike for Vec<DropCountingItem> {
    type Item = DropCountingItem;

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

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }
}

impl<'a> VecLike for FixedSliceVec<'a, DropCountingItem> {
    type Item = DropCountingItem;

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

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
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
