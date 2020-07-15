//! `FixedSliceVec` is a structure for defining variably populated
//! vectors backed by a slice of storage capacity.
use core::borrow::{Borrow, BorrowMut};
use core::convert::From;
use core::hash::{Hash, Hasher};
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

/// Vec-like structure backed by a storage slice of possibly
/// uninitialized data.
///
/// The maximum length (the capacity) is fixed at runtime to the
/// length of the provided storage slice.
pub struct FixedSliceVec<'a, T: Sized> {
    /// Backing storage, provides capacity
    pub(crate) storage: &'a mut [MaybeUninit<T>],
    /// The number of items that have been
    /// initialized
    pub(crate) len: usize,
}

impl<'a, T: Sized> Drop for FixedSliceVec<'a, T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<'a, T: Sized> FixedSliceVec<'a, T> {
    /// Create a `FixedSliceVec` backed by a slice of
    /// possibly-uninitialized data.  The backing storage slice is
    /// used as capacity for Vec-like operations,
    ///
    /// The initial length of the `FixedSliceVec` is 0.
    #[inline]
    pub fn new(storage: &'a mut [MaybeUninit<T>]) -> Self {
        FixedSliceVec { storage, len: 0 }
    }

    /// Create a well-aligned `FixedSliceVec` backed by a slice of the
    /// provided bytes.  The slice is as large as possible given the
    /// item type and alignment of the provided bytes.
    ///
    /// If you are interested in recapturing the prefix and suffix
    /// bytes on either side of the carved-out `FixedSliceVec` buffer,
    /// consider using `align_from_bytes` instead:
    ///
    /// ```
    /// # let mut bytes = [3u8, 1, 4, 1, 5, 9];
    /// let vec = fixed_slice_vec::FixedSliceVec::from_bytes(&mut bytes[..]);
    /// # let vec: fixed_slice_vec::FixedSliceVec<u16> = vec;
    /// ```
    ///
    /// The bytes are treated as if they might be uninitialized, so
    /// even if `T` is `u8`, the length of the returned `FixedSliceVec`
    /// will be zero.
    #[inline]
    pub fn from_bytes(bytes: &'a mut [u8]) -> FixedSliceVec<'a, T> {
        let (_prefix, fixed_slice_vec, _suffix) = FixedSliceVec::align_from_bytes(bytes);
        fixed_slice_vec
    }

    /// Create a well-aligned `FixedSliceVec` backed by a slice of the
    /// provided uninitialized bytes. The typed slice is as large as
    /// possible given its item type and the alignment of the provided
    /// bytes.
    ///
    /// If you are interested in recapturing the prefix and suffix
    /// bytes on either side of the carved-out `FixedSliceVec` buffer,
    /// consider using `align_from_uninit_bytes`:
    ///
    #[inline]
    pub fn from_uninit_bytes(bytes: &'a mut [MaybeUninit<u8>]) -> FixedSliceVec<'a, T> {
        let (_prefix, fixed_slice_vec, _suffix) = FixedSliceVec::align_from_uninit_bytes(bytes);
        fixed_slice_vec
    }

    /// Create a well-aligned `FixedSliceVec` backed by a slice of the
    /// provided bytes.  The slice is as large as possible given the
    /// item type and alignment of the provided bytes. Returns the
    /// unused prefix and suffix bytes on either side of the
    /// carved-out `FixedSliceVec`.
    ///
    /// ```
    /// let mut bytes = [3u8, 1, 4, 1, 5, 9];
    /// let (prefix, vec, suffix) = fixed_slice_vec::FixedSliceVec::align_from_bytes(&mut bytes[..]);
    /// let vec: fixed_slice_vec::FixedSliceVec<u16> = vec;
    /// ```
    ///
    /// The bytes are treated as if they might be uninitialized, so
    /// even if `T` is `u8`, the length of the returned
    /// `FixedSliceVec` will be zero.
    #[inline]
    pub fn align_from_bytes(
        bytes: &'a mut [u8],
    ) -> (&'a mut [u8], FixedSliceVec<'a, T>, &'a mut [u8]) {
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (prefix, FixedSliceVec { storage, len: 0 }, suffix)
    }

    /// Create a well-aligned `FixedSliceVec` backed by a slice of the
    /// provided bytes.  The slice is as large as possible given the
    /// item type and alignment of the provided bytes. Returns the
    /// unused prefix and suffix bytes on either side of the
    /// carved-out `FixedSliceVec`.
    ///
    /// ```
    /// # use core::mem::MaybeUninit;
    /// let mut bytes: [MaybeUninit<u8>; 15] = unsafe { MaybeUninit::uninit().assume_init() };
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

    /// The length of the `FixedSliceVec`. The number of initialized
    /// values that have been added to it.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// The maximum amount of items that can live in this
    /// `FixedSliceVec`
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    /// Returns true if there are no items present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns true if the `FixedSliceVec` is full to capacity.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    /// Attempt to add a value to the `FixedSliceVec`.
    ///
    /// Returns an error if there is not enough capacity to hold
    /// another item.
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), TryPushError<T>> {
        if self.is_full() {
            return Err(TryPushError(value));
        }
        self.storage[self.len] = MaybeUninit::new(value);
        self.len += 1;
        Ok(())
    }

    /// Attempt to add a value to the `FixedSliceVec`.
    ///
    /// # Panics
    ///
    /// Panics if there is not sufficient capacity to hold another
    /// item.
    #[inline]
    pub fn push(&mut self, value: T) {
        self.try_push(value).unwrap();
    }

    /// Remove the last item from the `FixedSliceVec`.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let upcoming_len = self.len - 1;
        let v = Some(unsafe { self.storage[upcoming_len].as_ptr().read() });
        self.len = upcoming_len;
        v
    }

    /// Removes the `FixedSliceVec`'s tracking of all items in it
    /// while retaining the same capacity.
    #[inline]
    pub fn clear(&mut self) {
        unsafe {
            (self.as_mut_slice() as *mut [T]).drop_in_place();
        }
        self.len = 0;
    }

    /// Obtain an immutable slice view on the initialized portion of
    /// the `FixedSliceVec`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Obtain a mutable slice view on the initialized portion of the
    /// `FixedSliceVec`.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }
}

/// Error that occurs when a call to `try_push` fails due
/// to insufficient capacity in the `FixedSliceVec`.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct TryPushError<T>(pub T);

impl<T> core::fmt::Debug for TryPushError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("Push failed because `FixedSliceVec` was full")
    }
}

impl<'a, T: Sized> From<&'a mut [MaybeUninit<T>]> for FixedSliceVec<'a, T> {
    #[inline]
    fn from(v: &'a mut [MaybeUninit<T>]) -> Self {
        FixedSliceVec { storage: v, len: 0 }
    }
}

impl<'a, T: Sized> From<&'a mut [T]> for FixedSliceVec<'a, T> {
    #[inline]
    fn from(v: &'a mut [T]) -> Self {
        let len = v.len();
        FixedSliceVec {
            storage: unsafe {
                core::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut MaybeUninit<T>, len)
            },
            len,
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_uninit() {
        let mut data: [MaybeUninit<u8>; 32] = unsafe { MaybeUninit::uninit().assume_init() };
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
    fn from_init() {
        let mut data = [2, 7, 1, 9, 8, 3];
        let mut sv: FixedSliceVec<u8> = (&mut data[..]).into();
        assert_eq!(6, sv.len());
        assert_eq!(6, sv.capacity());
        assert_eq!(Some(3), sv.pop());
        assert_eq!(Some(8), sv.pop());
        assert_eq!(Some(9), sv.pop());
        assert_eq!(3, sv.len());
        assert_eq!(6, sv.capacity());
    }

    #[test]
    fn happy_path_from_bytes() {
        let mut data = [0u8; 31];
        let mut sv: FixedSliceVec<usize> = FixedSliceVec::from_bytes(&mut data[..]);
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
                    FixedSliceVec::align_from_bytes(storage);
                assert_eq!(
                    storage_len,
                    prefix.len() + 2 * fixed_slice_vec.capacity() + suffix.len()
                );
            }
        }
    }
}
