//! Functions relating to managing references to well-typed Rust values
//! stored inside arbitrary byte slices.
use core::mem::*;

/// Plenty can go wrong when attempting to embed a value in arbitrary bytes
#[derive(Debug, PartialEq)]
pub enum EmbedValueError<E> {
    /// Difficulty generating the necessary mutable reference
    /// to the embedded location.
    SplitUninitError(SplitUninitError),
    /// Initializing the value went wrong somehow.
    ConstructionError(E),
}

impl<E> From<SplitUninitError> for EmbedValueError<E> {
    #[inline]
    fn from(e: SplitUninitError) -> Self {
        EmbedValueError::SplitUninitError(e)
    }
}

/// Initialize a value into location within a provided byte slice,
/// and return a mutable reference to that value.
///
/// The user-provided constructor function also has access to the
/// portions of the byte slice after the region allocated for
/// the embedded value itself.
#[inline]
pub fn embed<'a, T, F, E>(destination: &'a mut [u8], f: F) -> Result<&'a mut T, EmbedValueError<E>>
where
    F: Fn(&'a mut [u8]) -> Result<T, E>,
{
    debug_assert!(!destination.as_mut_ptr().is_null());
    let (_prefix, uninit_ref, suffix) = split_uninit_from_bytes(destination)?;
    unsafe {
        let ptr = uninit_ref.as_mut_ptr();
        *ptr = f(suffix).map_err(EmbedValueError::ConstructionError)?;
        // We literally just initialized the value, so it's safe to call it init
        Ok(ptr
            .as_mut()
            .expect("Just initialized the value and the pointer is based on a non-null slice"))
    }
}

/// Initialize a value into location within a provided byte slice,
/// and return a mutable reference to that value.
///
/// The user-provided constructor function also has access to the
/// portions of the byte slice after the region allocated for
/// the embedded value itself.
#[inline]
pub fn embed_uninit<'a, T, F, E>(
    destination: &'a mut [MaybeUninit<u8>],
    f: F,
) -> Result<&'a mut T, EmbedValueError<E>>
where
    F: Fn(&'a mut [MaybeUninit<u8>]) -> Result<T, E>,
{
    debug_assert!(!destination.as_mut_ptr().is_null());
    let (_prefix, uninit_ref, suffix) = split_uninit_from_uninit_bytes(destination)?;
    unsafe {
        let ptr = uninit_ref.as_mut_ptr();
        *ptr = f(suffix).map_err(EmbedValueError::ConstructionError)?;
        // We literally just initialized the value, so it's safe to call it init
        Ok(ptr
            .as_mut()
            .expect("Just initialized the value and the pointer is based on a non-null slice"))
    }
}

/// Plenty can go wrong when attempting to find space for a value in arbitrary bytes.
#[derive(Debug, PartialEq)]
pub enum SplitUninitError {
    /// Zero sized types shouldn't be placed anywhere into a byte slice anyhow.
    ZeroSizedTypesUnsupported,
    /// Could not theoretically fit the target value into the provided byte slice
    /// due to a combination of the type's alignment and size.
    InsufficientSpace,
}

/// Split out a mutable reference to an uninitialized struct at an available
/// location within a provided slice of bytes.
///
/// Does not access or mutate the content of the provided `destination` byte
/// slice.
#[inline]
pub fn split_uninit_from_bytes<T>(
    destination: &mut [u8],
) -> Result<(&mut [u8], &mut MaybeUninit<T>, &mut [u8]), SplitUninitError> {
    debug_assert!(!destination.as_mut_ptr().is_null());
    // Here we rely on the assurance that MaybeUninit has the same layout
    // as its parameterized type, and our knowledge of the implementation
    // of `split_uninit_from_uninit_bytes`, namely that it never accesses
    // or mutates any content passed to it.
    let (prefix, uninit_ref, suffix): (_, &mut MaybeUninit<T>, _) =
        split_uninit_from_uninit_bytes(unsafe { transmute(destination) })?;
    Ok(unsafe { (transmute(prefix), transmute(uninit_ref), transmute(suffix)) })
}

/// Split out a mutable reference to an uninitialized struct at an available
/// location within a provided slice of maybe-uninitialized bytes.
///
/// Does not access or mutate the content of the provided `destination` byte
/// slice.
#[inline]
pub fn split_uninit_from_uninit_bytes<T>(
    destination: &mut [MaybeUninit<u8>],
) -> Result<
    (
        &mut [MaybeUninit<u8>],
        &mut MaybeUninit<T>,
        &mut [MaybeUninit<u8>],
    ),
    SplitUninitError,
> {
    debug_assert!(!destination.as_mut_ptr().is_null());
    if size_of::<T>() == 0 {
        return Err(SplitUninitError::ZeroSizedTypesUnsupported);
    }
    let ptr = destination.as_mut_ptr();
    let offset = ptr.align_offset(align_of::<T>());
    if offset + size_of::<T>() > destination.len() {
        return Err(SplitUninitError::InsufficientSpace);
    }
    let (prefix, rest) = destination.split_at_mut(offset);
    let (middle, suffix) = rest.split_at_mut(size_of::<T>());
    let maybe_uninit = middle.as_mut_ptr() as *mut MaybeUninit<T>;
    Ok((
        prefix,
        unsafe {
            maybe_uninit
                .as_mut()
                .expect("Should be non-null since we rely on the input byte slice being non-null.")
        },
        suffix,
    ))
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use super::*;
    #[derive(PartialEq)]
    struct ZST;

    #[derive(Default)]
    struct TooBig {
        colossal: [Colossal; 32],
    }
    #[derive(Default)]
    struct Colossal {
        huge: [Huge; 32],
    }
    #[derive(Default)]
    struct Huge {
        large: [Large; 32],
    }
    #[derive(Default)]
    struct Large {
        medium: [u64; 32],
    }

    #[test]
    fn zero_sized_types_not_permitted() {
        let mut bytes = [0u8; 64];
        if let Err(e) = split_uninit_from_bytes::<ZST>(&mut bytes[..]) {
            assert_eq!(SplitUninitError::ZeroSizedTypesUnsupported, e);
        } else {
            panic!("Expected an err");
        }
        if let Err(e) = embed(&mut bytes[..], |_| -> Result<ZST, ()> { Ok(ZST) }) {
            assert_eq!(
                EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported),
                e
            );
        } else {
            panic!("Expected an err");
        }

        let mut uninit_bytes: [MaybeUninit<u8>; 64] =
            unsafe { MaybeUninit::uninit().assume_init() };
        if let Err(e) = split_uninit_from_uninit_bytes::<ZST>(&mut uninit_bytes[..]) {
            assert_eq!(SplitUninitError::ZeroSizedTypesUnsupported, e);
        } else {
            panic!("Expected an err");
        }
        if let Err(e) = embed_uninit(&mut uninit_bytes[..], |_| -> Result<ZST, ()> { Ok(ZST) }) {
            assert_eq!(
                EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported),
                e
            );
        } else {
            panic!("Expected an err");
        }
    }

    #[test]
    fn split_not_enough_space_detected() {
        let mut bytes = [0u8; 64];
        if let Err(e) = split_uninit_from_bytes::<TooBig>(&mut bytes[..]) {
            assert_eq!(SplitUninitError::InsufficientSpace, e);
        } else {
            panic!("Expected an err");
        }
    }

    #[test]
    fn split_uninit_not_enough_space_detected() {
        let mut uninit_bytes: [MaybeUninit<u8>; 64] =
            unsafe { MaybeUninit::uninit().assume_init() };
        if let Err(e) = split_uninit_from_uninit_bytes::<TooBig>(&mut uninit_bytes[..]) {
            assert_eq!(SplitUninitError::InsufficientSpace, e);
        } else {
            panic!("Expected an err");
        }
    }

    #[test]
    fn embed_not_enough_space_detected() {
        let mut bytes = [0u8; 64];
        if let Err(e) = embed(&mut bytes[..], |_| -> Result<Colossal, ()> {
            Ok(Colossal::default())
        }) {
            assert_eq!(
                EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace),
                e
            );
        } else {
            panic!("Expected an err");
        }
    }

    #[test]
    fn embed_uninit_not_enough_space_detected() {
        let mut uninit_bytes: [MaybeUninit<u8>; 64] =
            unsafe { MaybeUninit::uninit().assume_init() };
        if let Err(e) = embed_uninit(&mut uninit_bytes[..], |_| -> Result<Colossal, ()> {
            Ok(Colossal::default())
        }) {
            assert_eq!(
                EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace),
                e
            );
        } else {
            panic!("Expected an err");
        }
    }

    #[test]
    fn happy_path_split() {
        let mut bytes = [0u8; 512];
        let (prefix, _large_ref, suffix) =
            split_uninit_from_bytes::<Large>(&mut bytes[..]).unwrap();
        assert_eq!(
            prefix.len() + core::mem::size_of::<Large>() + suffix.len(),
            bytes.len()
        );
    }

    #[test]
    fn happy_path_split_uninit() {
        let mut uninit_bytes: [MaybeUninit<u8>; 512] =
            unsafe { MaybeUninit::uninit().assume_init() };
        let (prefix, _large_ref, suffix) =
            split_uninit_from_uninit_bytes::<Large>(&mut uninit_bytes[..]).unwrap();
        assert_eq!(
            prefix.len() + core::mem::size_of::<Large>() + suffix.len(),
            uninit_bytes.len()
        );
    }

    #[test]
    fn happy_path_embed() {
        const BACKING_BYTES_MAX_SIZE: usize = 512;
        let mut bytes = [2u8; BACKING_BYTES_MAX_SIZE];
        let large_ref = embed(&mut bytes[..], |b| -> Result<Large, ()> {
            assert!(b.iter().all(|b| *b == 2));
            let mut l = Large::default();
            l.medium[0] = 3;
            l.medium[1] = 1;
            l.medium[2] = 4;
            Ok(l)
        })
        .unwrap();
        assert_eq!(3, large_ref.medium[0]);
        assert_eq!(1, large_ref.medium[1]);
        assert_eq!(4, large_ref.medium[2]);
    }
    #[test]
    fn happy_path_embed_uninit() {
        const BACKING_BYTES_MAX_SIZE: usize = 512;
        let mut uninit_bytes: [MaybeUninit<u8>; BACKING_BYTES_MAX_SIZE] =
            unsafe { MaybeUninit::uninit().assume_init() };
        let large_ref = embed_uninit(&mut uninit_bytes[..], |_| -> Result<Large, ()> {
            let mut l = Large::default();
            l.medium[0] = 3;
            l.medium[1] = 1;
            l.medium[2] = 4;
            Ok(l)
        })
        .unwrap();
        assert_eq!(3, large_ref.medium[0]);
        assert_eq!(1, large_ref.medium[1]);
        assert_eq!(4, large_ref.medium[2]);
    }
}
