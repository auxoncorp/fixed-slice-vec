//! FixedSliceVec is a structure for defining variably populated vectors backed
//! by a slice of storage capacity.
use core::borrow::{Borrow, BorrowMut};
use core::convert::From;
use core::hash::{Hash, Hasher};
use core::iter::Extend;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

/// Vec-like structure backed by a storage slice of possibly uninitialized data.
///
/// The maximum length (the capacity) is fixed at runtime to the length of the
/// provided storage slice.
pub struct FixedSliceVec<'a, T: Sized> {
    /// Backing storage, provides capacity
    storage: &'a mut [MaybeUninit<T>],
    /// The number of items that have been
    /// initialized
    len: usize,
}

impl<'a, T: Sized> Drop for FixedSliceVec<'a, T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<'a, T: Sized> FixedSliceVec<'a, T> {
    /// Create a FixedSliceVec backed by a slice of possibly-uninitialized data.
    /// The backing storage slice is used as capacity for Vec-like operations,
    ///
    /// The initial length of the FixedSliceVec is 0.
    #[inline]
    pub fn new(storage: &'a mut [MaybeUninit<T>]) -> Self {
        FixedSliceVec { storage, len: 0 }
    }

    /// Create a well-aligned FixedSliceVec backed by a slice of the provided bytes.
    /// The slice is as large as possible given the item type and alignment of
    /// the provided bytes.
    ///
    /// If you are interested in recapturing the prefix and suffix bytes on
    /// either side of the carved-out FixedSliceVec buffer, consider using `align_from_bytes` instead:
    ///
    /// ```
    /// # let mut bytes = [3u8, 1, 4, 1, 5, 9];
    /// let vec = unsafe { fixed_slice_vec::FixedSliceVec::from_bytes(&mut bytes[..]) };
    /// # let vec: fixed_slice_vec::FixedSliceVec<u16> = vec;
    /// ```
    ///
    /// The bytes are treated as if they might be uninitialized, so even if `T` is `u8`,
    /// the length of the returned `FixedSliceVec` will be zero.
    ///
    /// # Safety
    ///
    /// If the item type `T` of the FixedSliceVec contains any padding bytes
    /// then those padding bytes may be observable in the provided slice
    /// after the `FixedSliceVec` is dropped. Observing padding bytes is
    /// undefined behavior.
    #[inline]
    pub unsafe fn from_bytes(bytes: &'a mut [u8]) -> FixedSliceVec<'a, T> {
        FixedSliceVec::align_from_bytes(bytes).1
    }

    /// Create a well-aligned FixedSliceVec backed by a slice of the provided
    /// uninitialized bytes. The typed slice is as large as possible given its
    /// item type and the alignment of the provided bytes.
    ///
    /// If you are interested in recapturing the prefix and suffix bytes on
    /// either side of the carved-out FixedSliceVec buffer, consider using `align_from_uninit_bytes`:
    ///
    #[inline]
    pub fn from_uninit_bytes(bytes: &'a mut [MaybeUninit<u8>]) -> FixedSliceVec<'a, T> {
        FixedSliceVec::align_from_uninit_bytes(bytes).1
    }

    /// Create a well-aligned FixedSliceVec backed by a slice of the provided bytes.
    /// The slice is as large as possible given the item type and alignment of
    /// the provided bytes. Returns the unused prefix and suffix bytes on
    /// either side of the carved-out FixedSliceVec.
    ///
    /// ```
    /// let mut bytes = [3u8, 1, 4, 1, 5, 9];
    /// let (prefix, vec, suffix) = unsafe { fixed_slice_vec::FixedSliceVec::align_from_bytes(&mut bytes[..]) };
    /// let vec: fixed_slice_vec::FixedSliceVec<u16> = vec;
    /// ```
    ///
    /// The bytes are treated as if they might be uninitialized, so even if `T` is `u8`,
    /// the length of the returned `FixedSliceVec` will be zero.
    ///
    /// # Safety
    ///
    /// If the item type `T` of the FixedSliceVec contains any padding bytes
    /// then those padding bytes may be observable in the provided slice
    /// after the `FixedSliceVec` is dropped. Observing padding bytes is
    /// undefined behavior.
    #[inline]
    pub unsafe fn align_from_bytes(
        bytes: &'a mut [u8],
    ) -> (&'a mut [u8], FixedSliceVec<'a, T>, &'a mut [u8]) {
        let (prefix, storage, suffix) = bytes.align_to_mut();
        (prefix, FixedSliceVec { storage, len: 0 }, suffix)
    }

    /// Create a well-aligned FixedSliceVec backed by a slice of the provided bytes.
    /// The slice is as large as possible given the item type and alignment of
    /// the provided bytes. Returns the unused prefix and suffix bytes on
    /// either side of the carved-out FixedSliceVec.
    ///
    /// ```
    /// # use core::mem::MaybeUninit;
    /// let mut bytes = [MaybeUninit::new(0u8); 15];
    /// let (prefix, vec, suffix) = fixed_slice_vec::FixedSliceVec::align_from_uninit_bytes(&mut
    /// bytes[..]);
    /// let vec: fixed_slice_vec::FixedSliceVec<u16> = vec;
    /// ```
    ///
    /// The length of the returned `FixedSliceVec` will be zero.
    #[inline]
    pub fn align_from_uninit_bytes(
        bytes: &'a mut [MaybeUninit<u8>],
    ) -> (
        &'a mut [MaybeUninit<u8>],
        FixedSliceVec<'a, T>,
        &'a mut [MaybeUninit<u8>],
    ) {
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (prefix, FixedSliceVec { storage, len: 0 }, suffix)
    }

    /// Returns an unsafe mutable pointer to the FixedSliceVec's buffer.
    ///
    /// The caller must ensure that the FixedSliceVec and the backing
    /// storage data for the FixedSliceVec (provided at construction)
    /// outlives the pointer this function returns.
    ///
    /// Furthermore, the contents of the buffer are not guaranteed
    /// to have been initialized at indices < len.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::mem::MaybeUninit;
    /// let mut storage = [MaybeUninit::new(0u8); 16];
    /// let mut x: fixed_slice_vec::FixedSliceVec<u16> = fixed_slice_vec::FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    /// assert!(x.try_extend([1u16, 2, 4, 8].iter().copied()).is_ok());
    /// let size = x.len();
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Set elements via raw pointer writes.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as u16;
    ///     }
    /// }
    /// assert_eq!(&*x, &[0,1,2,3]);
    /// ```
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.storage.as_mut_ptr() as *mut T
    }
    /// Returns a raw pointer to the FixedSliceVec's buffer.
    ///
    /// The caller must ensure that the FixedSliceVec and the backing
    /// storage data for the FixedSliceVec (provided at construction)
    /// outlives the pointer this function returns.
    ///
    /// Furthermore, the contents of the buffer are not guaranteed
    /// to have been initialized at indices < len.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to using this pointer or any pointer derived from it.
    ///
    /// If you need to mutate the contents of the slice with pointers, use [`as_mut_ptr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use core::mem::MaybeUninit;
    /// let mut storage = [MaybeUninit::new(0u8); 16];
    /// let mut x: fixed_slice_vec::FixedSliceVec<u16> = fixed_slice_vec::FixedSliceVec::from_uninit_bytes(&mut storage[..]);
    /// x.extend([1u16, 2, 4].iter().copied());
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: #method.as_mut_ptr
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.storage.as_ptr() as *const T
    }

    /// The length of the FixedSliceVec. The number of initialized
    /// values that have been added to it.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// The maximum amount of items that can live in this FixedSliceVec
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    /// Returns true if there are no items present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns true if the FixedSliceVec is full to capacity.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    /// Attempt to add a value to the FixedSliceVec.
    ///
    /// Returns an error if there is not enough capacity to hold another item.
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), StorageError<T>> {
        if self.is_full() {
            return Err(StorageError(value));
        }
        self.storage[self.len] = MaybeUninit::new(value);
        self.len += 1;
        Ok(())
    }

    /// Attempt to add a value to the FixedSliceVec.
    ///
    /// # Panics
    ///
    /// Panics if there is not sufficient capacity to hold another item.
    #[inline]
    pub fn push(&mut self, value: T) {
        self.try_push(value).unwrap();
    }

    /// Attempt to add as many values as will fit from an iterable.
    ///
    /// Returns Ok(()) if all of the items in the iterator can fit into `self`.
    /// Returns an Err containing the iterator if `self` fills up and there
    /// are items remaining in the iterator.
    #[inline]
    pub fn try_extend(
        &mut self,
        iterable: impl IntoIterator<Item = T>,
    ) -> Result<(), impl Iterator<Item = T>> {
        let mut iter = iterable.into_iter().peekable();
        loop {
            if iter.peek().is_some() {
                if self.is_full() {
                    return Err(iter);
                } else if let Some(item) = iter.next() {
                    self.storage[self.len] = MaybeUninit::new(item);
                    self.len += 1;
                } else {
                    unreachable!("`FixedSliceVec::try_extend` peeked above to ensure that `next` would return Some")
                }
            } else {
                return Ok(());
            }
        }
    }

    /// Remove the last item from the FixedSliceVec.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let upcoming_len = self.len - 1;
        let v = Some(unsafe {
            let item_slice = &self.storage[upcoming_len..self.len];
            (item_slice.as_ptr() as *const T).read()
        });
        self.len = upcoming_len;
        v
    }

    /// Removes the FixedSliceVec's tracking of all items in it while retaining the
    /// same capacity.
    #[inline]
    pub fn clear(&mut self) {
        unsafe {
            (self.as_mut_slice() as *mut [T]).drop_in_place();
        }
        self.len = 0;
    }

    /// Shortens the FixedSliceVec, keeping the first `len` elements and dropping the rest.
    ///
    /// If len is greater than the current length, this has no effect.
    /// Note that this method has no effect on the capacity of the FixedSliceVec.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len > self.len {
            return;
        }
        unsafe {
            (&mut self.as_mut_slice()[len..] as *mut [T]).drop_in_place();
        }
        self.len = len;
    }
    /// Removes and returns the element at position `index` within the FixedSliceVec,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn remove(&mut self, index: usize) -> T {
        // Error message and overall impl strategy following along with std vec,
        if index >= self.len {
            panic!(
                "removal index (is {}) should be < len (is {})",
                index, self.len
            );
        }
        unsafe { self.unchecked_remove(index) }
    }

    /// Removes and returns the element at position `index` within the FixedSliceVec,
    /// shifting all elements after it to the left.
    pub fn try_remove(&mut self, index: usize) -> Result<T, IndexError> {
        if index >= self.len {
            return Err(IndexError);
        }
        Ok(unsafe { self.unchecked_remove(index) })
    }

    /// Remove and return an element without checking if it's actually there.
    #[inline]
    unsafe fn unchecked_remove(&mut self, index: usize) -> T {
        let ptr = self.as_mut_ptr().add(index);
        let out = core::ptr::read(ptr);
        core::ptr::copy(ptr.offset(1), ptr, self.len - index - 1);
        self.len -= 1;
        out
    }
    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> T {
        if index >= self.len {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                index, self.len
            );
        }
        unsafe { self.unchecked_swap_remove(index) }
    }
    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    pub fn try_swap_remove(&mut self, index: usize) -> Result<T, IndexError> {
        if index >= self.len {
            return Err(IndexError);
        }
        Ok(unsafe { self.unchecked_swap_remove(index) })
    }

    /// swap_remove, without the length-checking
    #[inline]
    unsafe fn unchecked_swap_remove(&mut self, index: usize) -> T {
        let target_ptr = self.as_mut_ptr().add(index);
        let end_ptr = self.as_ptr().add(self.len - 1);
        let end_value = core::ptr::read(end_ptr);
        self.len -= 1;
        core::ptr::replace(target_ptr, end_value)
    }

    /// Obtain an immutable slice view on the initialized portion of the
    /// FixedSliceVec.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Obtain a mutable slice view on the initialized portion of the
    /// FixedSliceVec.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }
}

/// Error that occurs when a call that attempts to increase
/// the number of items in the FixedSliceVec fails
/// due to insufficient storage capacity.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct StorageError<T>(pub T);

impl<T> core::fmt::Debug for StorageError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("Push failed because FixedSliceVec was full")
    }
}

/// Error that occurs when a call that attempts to access
/// the FixedSliceVec in a manner that does not respect
/// the current length of the vector, i.e. its current
/// number of initialized items.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct IndexError;

impl core::fmt::Debug for IndexError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str(
            "Access to the FixedSliceVec failed because an invalid index or length was provided",
        )
    }
}

impl<'a, T: Sized> From<&'a mut [MaybeUninit<T>]> for FixedSliceVec<'a, T> {
    #[inline]
    fn from(v: &'a mut [MaybeUninit<T>]) -> Self {
        FixedSliceVec { storage: v, len: 0 }
    }
}

impl<'a, T: Sized> Hash for FixedSliceVec<'a, T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<'a, T: Sized> PartialEq for FixedSliceVec<'a, T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<'a, T: Sized> PartialEq<[T]> for FixedSliceVec<'a, T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        **self == *other
    }
}

impl<'a, T: Sized> Eq for FixedSliceVec<'a, T> where T: Eq {}

impl<'a, T: Sized> Borrow<[T]> for FixedSliceVec<'a, T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<'a, T: Sized> BorrowMut<[T]> for FixedSliceVec<'a, T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<'a, T: Sized> AsRef<[T]> for FixedSliceVec<'a, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<'a, T: Sized> AsMut<[T]> for FixedSliceVec<'a, T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<'a, T: Sized> core::fmt::Debug for FixedSliceVec<'a, T>
where
    T: core::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        (**self).fmt(f)
    }
}

impl<'a, T: Sized> PartialOrd for FixedSliceVec<'a, T>
where
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &FixedSliceVec<'a, T>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(other)
    }

    #[inline]
    fn lt(&self, other: &Self) -> bool {
        (**self).lt(other)
    }

    #[inline]
    fn le(&self, other: &Self) -> bool {
        (**self).le(other)
    }

    #[inline]
    fn gt(&self, other: &Self) -> bool {
        (**self).gt(other)
    }

    #[inline]
    fn ge(&self, other: &Self) -> bool {
        (**self).ge(other)
    }
}

impl<'a, T: Sized> Deref for FixedSliceVec<'a, T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.storage.as_ptr() as *const T, self.len) }
    }
}

impl<'a, T: Sized> DerefMut for FixedSliceVec<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.storage.as_mut_ptr() as *mut T, self.len) }
    }
}

/// Adds as many items from the provided iterable as can fit.
///
/// Gives no indication of how many were extracted or if some
/// could not fit.
///
/// Use `FixedSliceVec::try_extend` if you require more fine-
/// grained signal about the outcome of attempted extension.
impl<'a, T: Sized> Extend<T> for FixedSliceVec<'a, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let _ = self.try_extend(iter);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_uninit() {
        let mut data = [MaybeUninit::new(0u8); 32];
        let mut sv: FixedSliceVec<u8> = (&mut data[..]).into();
        assert_eq!(0, sv.len());
        assert_eq!(32, sv.capacity());
        assert!(sv.is_empty());
        let sv_as_slice: &[u8] = &sv;
        let empty_slice: &[u8] = &[];
        assert_eq!(empty_slice, sv_as_slice);
        assert_eq!(Ok(()), sv.try_push(3));
        assert_eq!(Ok(()), sv.try_push(1));
        assert_eq!(Ok(()), sv.try_push(4));
        let non_empty_slice: &[u8] = &[3u8, 1, 4];
        assert_eq!(non_empty_slice, &sv as &[u8]);
        let sv_as_mut_slice: &mut [u8] = &mut sv;
        sv_as_mut_slice[1] = 2;
        let non_empty_slice: &[u8] = &[3u8, 2, 4];
        assert_eq!(non_empty_slice, &sv as &[u8]);

        sv.clear();
        assert_eq!(0, sv.len());
        assert!(sv.is_empty());
    }

    #[test]
    fn happy_path_from_bytes() {
        let mut data = [0u8; 31];
        let mut sv: FixedSliceVec<usize> = unsafe { FixedSliceVec::from_bytes(&mut data[..]) };
        assert!(sv.is_empty());
        // capacity might be 0 if miri messes with the align-ability of pointers
        if sv.capacity() > 0 {
            for i in 0..sv.capacity() {
                assert_eq!(Ok(()), sv.try_push(i));
            }
        }
        assert!(sv.is_full());
    }

    #[test]
    fn align_captures_suffix_and_prefix() {
        let mut data = [
            3u8, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3,
        ];
        let original_len = data.len();
        for i in 0..original_len {
            for len in 0..original_len - i {
                let storage = &mut data[i..i + len];
                let storage_len = storage.len();
                let (prefix, fixed_slice_vec, suffix): (_, FixedSliceVec<u16>, _) =
                    unsafe { FixedSliceVec::align_from_bytes(storage) };
                assert_eq!(
                    storage_len,
                    prefix.len() + 2 * fixed_slice_vec.capacity() + suffix.len()
                );
            }
        }
    }
    fn uninit_storage() -> [MaybeUninit<u8>; 4] {
        [MaybeUninit::new(0u8); 4]
    }

    #[test]
    fn as_ptr_reveals_expected_internal_content() {
        let expected = [0u8, 1, 2, 3];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());

        let ptr = fsv.as_ptr();
        for i in 0..fsv.len() {
            assert_eq!(expected[i], unsafe { *ptr.add(i) });
        }

        let mut fsv = fsv;
        fsv[3] = 99;
        assert_eq!(99, unsafe { *ptr.add(3) })
    }

    #[test]
    fn as_mut_ptr_allows_changes_to_internal_content() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());

        let ptr = fsv.as_mut_ptr();
        assert_eq!(8, unsafe { ptr.add(3).read() });
        unsafe {
            ptr.add(3).write(99);
        }
        assert_eq!(99, fsv[3]);

        fsv[1] = 200;
        assert_eq!(200, unsafe { ptr.add(1).read() });
    }

    #[test]
    fn manual_truncate() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());

        fsv.truncate(100);
        assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
        fsv.truncate(2);
        assert_eq!(&[0u8, 2], fsv.as_slice());
        fsv.truncate(2);
        assert_eq!(&[0u8, 2], fsv.as_slice());
        fsv.truncate(0);
        assert!(fsv.is_empty());
    }

    #[test]
    fn manual_try_remove() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());

        assert_eq!(Err(IndexError), fsv.try_remove(100));
        assert_eq!(Err(IndexError), fsv.try_remove(4));
        assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
        assert_eq!(Ok(2), fsv.try_remove(1));
        assert_eq!(&[0u8, 4, 8], fsv.as_slice());
    }

    #[test]
    #[should_panic]
    fn manual_swap_remove_outside_range() {
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend([0u8, 2, 4, 8].iter().copied()).is_ok());
        fsv.swap_remove(100);
    }

    #[test]
    #[should_panic]
    fn manual_swap_remove_empty() {
        let mut storage = uninit_storage();
        let mut fsv: FixedSliceVec<u16> = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.capacity() > 0);
        assert_eq!(0, fsv.len());
        fsv.swap_remove(0);
    }

    #[test]
    fn manual_swap_remove_inside_range() {
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend([0u8, 2, 4, 8].iter().copied()).is_ok());
        assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
        assert_eq!(2, fsv.swap_remove(1));
        assert_eq!(&[0u8, 8, 4], fsv.as_slice());
        assert_eq!(0, fsv.swap_remove(0));
        assert_eq!(&[4u8, 8], fsv.as_slice());
        assert_eq!(4, fsv.swap_remove(0));
        assert_eq!(&[8u8], fsv.as_slice());
        assert_eq!(8, fsv.swap_remove(0));
        assert!(fsv.as_slice().is_empty());
    }

    #[test]
    fn manual_try_swap_remove() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());

        assert_eq!(Err(IndexError), fsv.try_swap_remove(100));
        assert_eq!(Err(IndexError), fsv.try_swap_remove(4));
        assert_eq!(&[0u8, 2, 4, 8], fsv.as_slice());
        assert_eq!(Ok(2), fsv.try_swap_remove(1));
        assert_eq!(&[0u8, 8, 4], fsv.as_slice());
        assert_eq!(Ok(0), fsv.try_swap_remove(0));
        assert_eq!(&[4u8, 8], fsv.as_slice());
        assert_eq!(Ok(4), fsv.try_swap_remove(0));
        assert_eq!(&[8u8], fsv.as_slice());
        assert_eq!(Ok(8), fsv.try_swap_remove(0));
        assert!(fsv.as_slice().is_empty());
        assert_eq!(Err(IndexError), fsv.try_swap_remove(0));
    }

    #[test]
    fn try_extend_with_exactly_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());
        assert_eq!(&expected[..], &fsv[..]);
    }

    #[test]
    fn try_extend_with_more_than_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = [MaybeUninit::new(0u8); 100];
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        assert!(fsv.try_extend(expected.iter().copied()).is_ok());
        assert_eq!(&expected[..], &fsv[..]);
    }

    #[test]
    fn try_extend_with_not_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = [MaybeUninit::new(0u8); 2];
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        let mut out_iter = fsv.try_extend(expected.iter().copied()).unwrap_err();
        assert_eq!(Some(4), out_iter.next());
        assert_eq!(Some(8), out_iter.next());
        assert_eq!(None, out_iter.next());
        assert_eq!(&expected[0..2], &fsv[..]);
    }
    #[test]
    fn extend_with_exactly_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = uninit_storage();
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        fsv.extend(expected.iter().copied());
        assert_eq!(&expected[..], &fsv[..]);
    }

    #[test]
    fn extend_with_more_than_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = [MaybeUninit::new(0u8); 100];
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        fsv.extend(expected.iter().copied());
        assert_eq!(&expected[..], &fsv[..]);
    }

    #[test]
    fn extend_with_not_enough_room() {
        let expected = [0u8, 2, 4, 8];
        let mut storage = [MaybeUninit::new(0u8); 2];
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        fsv.extend(expected.iter().copied());
        assert_eq!(&expected[0..2], &fsv[..]);
    }

    #[test]
    fn from_uninit_bytes_empty_slice() {
        let storage: &mut [MaybeUninit<u8>] = &mut [];
        let mut fsv: FixedSliceVec<u8> = FixedSliceVec::from_uninit_bytes(storage);
        assert_eq!(0, fsv.capacity());
        assert_eq!(0, fsv.len());
        assert!(fsv.try_push(31).is_err());
    }
    #[test]
    fn from_uninit_bytes_smaller_than_item_slice() {
        let mut storage = [MaybeUninit::new(0u8); 1];
        let mut fsv: FixedSliceVec<u16> = FixedSliceVec::from_uninit_bytes(&mut storage);
        assert_eq!(0, fsv.capacity());
        assert_eq!(0, fsv.len());
        assert!(fsv.try_push(31).is_err());
    }
    #[test]
    fn from_uninit_bytes_larger_than_item_slice() {
        let mut storage = [MaybeUninit::new(0u8); 9];
        let mut fsv: FixedSliceVec<u16> = FixedSliceVec::from_uninit_bytes(&mut storage);
        assert!(fsv.capacity() > 0);
        assert_eq!(0, fsv.len());
        assert!(fsv.try_push(31).is_ok());
        assert_eq!(&[31], &fsv[..]);
    }

    #[test]
    fn equality_sanity_checks() {
        let mut storage_a = [MaybeUninit::new(0u8); 2];
        let mut a: FixedSliceVec<u8> = FixedSliceVec::from_uninit_bytes(&mut storage_a);
        let mut storage_b = [MaybeUninit::new(0u8); 2];
        let mut b: FixedSliceVec<u8> = FixedSliceVec::from_uninit_bytes(&mut storage_b);

        assert_eq!(a, b);
        assert_eq!(&a, &b[..]);
        assert_eq!(&b, &a[..]);
        a.push(1u8);
        assert_ne!(a, b);
        assert_ne!(&a, &b[..]);
        assert_ne!(&b, &a[..]);
        b.push(1u8);
        assert_eq!(a, b);
        assert_eq!(&a, &b[..]);
        assert_eq!(&b, &a[..]);
    }

    #[test]
    fn borrow_ish_sanity_checks() {
        let mut expected = [0u8, 2, 4, 8];
        let mut storage = [MaybeUninit::new(0u8); 12];
        let mut fsv = FixedSliceVec::from_uninit_bytes(&mut storage[..]);
        fsv.extend(expected.iter().copied());

        assert_eq!(&expected[..], Borrow::<[u8]>::borrow(&fsv));
        assert_eq!(&mut expected[..], BorrowMut::<[u8]>::borrow_mut(&mut fsv));
        assert_eq!(&expected[..], fsv.as_ref());
        assert_eq!(&mut expected[..], fsv.as_mut());
    }

    #[test]
    fn comparison_sanity_checks() {
        let mut storage_a = [MaybeUninit::new(0u8); 2];
        let mut a: FixedSliceVec<u8> = FixedSliceVec::from_uninit_bytes(&mut storage_a);
        let mut storage_b = [MaybeUninit::new(0u8); 2];
        let mut b: FixedSliceVec<u8> = FixedSliceVec::from_uninit_bytes(&mut storage_b);
        use core::cmp::Ordering;
        assert_eq!(Some(Ordering::Equal), a.partial_cmp(&b));
        b.push(1);
        assert!(a.lt(&b));
        assert!(b.gt(&a));
        a.push(1);
        assert!(a.ge(&b));
        assert!(a.le(&b));
        a[0] = 2;
        assert!(a.gt(&b));
        assert!(b.lt(&a));
    }
}
