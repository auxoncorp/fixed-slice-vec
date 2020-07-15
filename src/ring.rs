//! A ring buffer backed by a FixedSliceVec.
use core::{convert::TryFrom, mem::MaybeUninit};

use crate::vec::FixedSliceVec;

/// A ring buffer backed by a FixedSliceVec.
pub struct FixedSliceRingBuffer<'a, T> {
    vec: FixedSliceVec<'a, T>,
    head: usize,
    len: usize,
    is_power_of_two_size: bool,
}

/// TODO Reuse vec::trypusherror
#[derive(Debug)]
pub struct Error;

impl<'a, T> FixedSliceRingBuffer<'a, T> {
    /// Create a `FixedSliceRingBuffer` backed by a slice of
    /// possibly-uninitialized data.
    #[inline]
    pub fn new(storage: &'a mut [MaybeUninit<T>]) -> Self {
        let is_power_of_two_size = storage.len().is_power_of_two();
        FixedSliceRingBuffer {
            is_power_of_two_size,
            vec: FixedSliceVec { storage, len: 0 },
            head: 0,
            len: 0,
        }
    }

    /// Try to add an item to the tail of the buffer.
    pub fn try_push(&mut self, item: T) -> Result<(), Error> {
        if self.len == self.vec.capacity() {
            return Err(Error);
        }
        self.vec.storage[self.wrap(self.len)] = MaybeUninit::new(item);
        self.len += 1;
        Ok(())
    }

    /// Remove the item at the head of the buffer.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let item = unsafe { self.vec.storage[self.head].as_ptr().read() };
        self.head = self.wrap(self.head + 1);
        self.len -= 1;
        Some(item)
    }

    /// Return the current length of the buffer.
    pub fn len(&self) -> usize {
        self.len
    }

    fn wrap(&self, idx: usize) -> usize {
        if self.is_power_of_two_size {
            (idx) & (self.vec.capacity() - 1)
        } else {
            (idx) % self.vec.capacity()
        }
    }
}

impl<'a, T> TryFrom<FixedSliceVec<'a, T>> for FixedSliceRingBuffer<'a, T> {
    type Error = (Self, Error);
    fn try_from(vec: FixedSliceVec<'a, T>) -> Result<Self, (Self, Error)> {
        let is_power_of_two_size = vec.capacity().is_power_of_two();
        if vec.is_empty() {
            return Ok(FixedSliceRingBuffer {
                vec,
                is_power_of_two_size,
                head: 0,
                len: 0,
            });
        }
        Err((
            FixedSliceRingBuffer {
                vec,
                is_power_of_two_size,
                head: 0,
                len: 0,
            },
            Error,
        ))
    }
}

#[cfg(test)]
mod test {

    use core::mem::MaybeUninit;

    use super::*;

    #[test]
    fn push_n_pop_power_of_2() {
        let mut storage = [MaybeUninit::<u8>::uninit(); 4];
        let mut ring = FixedSliceRingBuffer::new(&mut storage);
        ring.try_push(1).unwrap();
        ring.try_push(2).unwrap();
        ring.try_push(3).unwrap();
        ring.try_push(4).unwrap();
        assert_eq!(ring.len(), 4);
        let one = ring.pop().unwrap();
        assert_eq!(ring.len(), 3);
        assert_eq!(one, 1);
        ring.try_push(5).unwrap();
        assert_eq!(ring.len(), 4);
        let err = ring.try_push(1);
        assert!(err.is_err());
        let two = ring.pop().unwrap();
        assert_eq!(ring.len(), 3);
        assert_eq!(two, 2);
    }

    #[test]
    fn push_n_pop_not_power_of_2() {
        let mut storage = [MaybeUninit::<u8>::uninit(); 3];
        let mut ring = FixedSliceRingBuffer::new(&mut storage);
        ring.try_push(1).unwrap();
        ring.try_push(2).unwrap();
        ring.try_push(3).unwrap();
        assert_eq!(ring.len(), 3);
        let one = ring.pop().unwrap();
        assert_eq!(ring.len(), 2);
        assert_eq!(one, 1);
        ring.try_push(4).unwrap();
        assert_eq!(ring.len(), 3);
        let err = ring.try_push(1);
        assert!(err.is_err());
        let two = ring.pop().unwrap();
        assert_eq!(ring.len(), 2);
        assert_eq!(two, 2);
    }
}
