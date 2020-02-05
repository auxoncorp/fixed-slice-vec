//! `SliceVec` is a dynamic length Vec with runtime-determined maximum capacity backed by a slice.
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
//! `slice-vec` is a Rust library, built and tested via Cargo. It
//! has no dependencies outside of the Rust core library.
//!
//! To add `slice-vec` to your Rust project, add a dependency to it
//! in your Cargo.toml file.
//!
//! ```toml
//! slice-vec = "0.2"
//! ```
//!
//! ## Usage
//!
//! ### SliceVec
//!
//! In your Rust project source code, you can create a SliceVec a number of ways (see
//! the project Rust API docs for details).
//! The most common form of construction is from a slice of bare bytes.
//!
//! ```
//! use slice_vec::SliceVec;
//! let mut bytes = [0u8; 1024];
//! let byte_slice = &mut bytes[..512];
//! let mut vec: SliceVec<f64> = SliceVec::from_bytes(byte_slice);
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
//! Note that the types stored in a `SliceVec` must be have the `Copy`
//! marker trait constraint.
//!
//! ### slice_single module
//!
//! As a companion to `SliceVec`, the `slice_single` submodule provides
//! functions for working with individual Rust values backed by arbitrary
//! byte slices. See the API Docs for details and examples.
//!
//! ## License
//!
//! Copyright 2020 Auxon Corporation, released under the [Apache 2.0 license](./LICENSE).
#![no_std]
#![deny(warnings)]
#![deny(missing_docs)]

pub mod slice_single;
pub mod slice_vec;

pub use crate::slice_vec::*;
