//! `FixedSliceVec` is a dynamic length Vec with runtime-determined maximum capacity backed by a slice.
//!
//! ## Overview
//!
//! This library is focused on meeting the following, narrow use case:
//! * **`no_std`** : Rust programming without the std library.
//! * **No global allocator**: No access to the `alloc` crate
//! * **Runtime capacity** : Maximum possible items in a collection or maximum
//! possible backing bytes of storage is unknown until runtime.
//!
//! ## Getting Started
//!
//! `fixed-slice-vec` is a Rust library, built and tested via Cargo. It
//! has no dependencies outside of the Rust core library.
//!
//! To add `fixed-slice-vec` to your Rust project, add a dependency to it
//! in your Cargo.toml file.
//!
//! ```toml
//! fixed-slice-vec = "0.2"
//! ```
//!
//! ## Usage
//!
//! ### FixedSliceVec
//!
//! In your Rust project source code, you can create a FixedSliceVec a number of
//! ways (see the project Rust API docs for details).
//! The most common form of construction is from a slice of bare bytes.
//!
//! ```rust
//! use fixed_slice_vec::FixedSliceVec;
//! let mut bytes = [0u8; 1024];
//! let byte_slice = &mut bytes[..512];
//! let mut vec: FixedSliceVec<f64> = FixedSliceVec::from_bytes(byte_slice);
//!
//! assert_eq!(0, vec.len());
//! assert!(vec.capacity() >= 63, "The exact capacity will depend on source-slice alignment");
//!
//! vec.try_push(2.7f64).expect("Ran out of capacity unexpectedly");
//! assert_eq!(1, vec.len());
//!
//! vec.clear();
//! assert!(vec.is_empty());
//! ```
//!
//! Note that the types stored in a `FixedSliceVec` must be have the `Copy`
//! marker trait constraint.
//!
//! ### single module
//!
//! As a companion to `FixedSliceVec`, the `single` submodule provides
//! functions for working with individual Rust values backed by arbitrary
//! byte slices. See the API Docs for details and examples.
//!
//! ### Comparison
//!
//! Several other `Vec`-like crates exist and should be considered
//! as possible alternatives to `FixedSliceVec`.
//!
//! * The standard library's [Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html)
//! has a runtime dynamic capacity backed by an allocator. This should probably
//! be your first choice if you have access to an allocator.
//! * [ArrayVec](https://crates.io/crates/arrayvec) has a compile-time
//! fixed capacity. It is widely used and available on stable.
//! * [StaticVec](https://crates.io/crates/staticvec) has a compile-time
//! fixed capacity. It uses recent const generic features and is currently
//! nightly-only.
//! * [SliceVec](https://crates.io/crates/slicevec) has runtime fixed capacity.
//! This is the closest in its target use case to `FixedSliceVec`. We
//! only discovered it existed after developing `FixedSliceVec`, so there's some
//! evidence of convergent design or needs. It appears largely
//! unmaintained over the last few years, and does not make use of the
//! [MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)
//! pattern for handling uninitialized data in Rust. Presently it supports a few
//! more of the convenience methods available in standard `Vec` than
//! `FixedSliceVec`. It does not support creating an instance from raw bytes.
//!
//!
//! ## License
//!
//! Copyright 2020 Auxon Corporation, released under the [Apache 2.0 license](./LICENSE).
#![no_std]
#![deny(warnings)]
#![deny(missing_docs)]

pub mod single;
pub mod vec;

pub use crate::vec::*;
