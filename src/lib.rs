/*
 * Copyright 2021-2024 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is licensed under the Apache License, Version 2.0
 * (the "License"); you may not use tagged-pointer except in compliance
 * with the License. You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#![cfg_attr(not(all(test, feature = "compiletest_rs")), no_std)]
#![cfg_attr(has_unsafe_op_in_unsafe_fn, deny(unsafe_op_in_unsafe_fn))]
#![warn(clippy::pedantic)]
#![allow(clippy::default_trait_access)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::must_use_candidate)]

//! This crate provides an implementation of [tagged pointers]: pointers that
//! also contain an integer tag in a space-efficient manner.
//!
//! [tagged pointers]: https://en.wikipedia.org/wiki/Tagged_pointer
//!
//! Unless the fallback implementation is used (see the
//! [Assumptions](#assumptions) section below), both [`TaggedPtr`] and
//! [`Option<TaggedPtr>`] will be the size of a pointer.
//!
//! This crate depends only on [`core`], so it can be used in `no_std`
//! environments.
//!
//! [`core`]: https://doc.rust-lang.org/core/
//!
//! Example
//! -------
//!
//! ```rust
//! # #[cfg(not(feature = "fallback"))]
//! use core::mem::size_of;
//! use core::ptr::NonNull;
//! use tagged_pointer::TaggedPtr;
//!
//! #[repr(align(4))]
//! struct Item(u32, u32);
//!
//! # #[cfg(not(feature = "fallback"))]
//! # {
//! // `TaggedPtr` and `Option<TaggedPtr>` are both the size of a pointer:
//! assert_eq!(size_of::<TaggedPtr<Item, 2>>(), size_of::<*mut ()>());
//! assert_eq!(size_of::<Option<TaggedPtr<Item, 2>>>(), size_of::<*mut ()>());
//! # }
//!
//! let item1 = Item(1, 2);
//! let item2 = Item(3, 4);
//!
//! // We can store two bits of the tag, since `Item` has an alignment of 4.
//! let tp1 = TaggedPtr::<_, 2>::new(NonNull::from(&item1), 1);
//! let tp2 = TaggedPtr::<_, 2>::new(NonNull::from(&item2), 3);
//!
//! let (ptr1, tag1) = tp1.get();
//! let (ptr2, tag2) = tp2.get();
//!
//! assert_eq!((ptr1, tag1), (NonNull::from(&item1), 1));
//! assert_eq!((ptr2, tag2), (NonNull::from(&item2), 3));
//! ```
//!
//! Assumptions
//! -----------
//!
//! This crate relies on [`pointer::align_offset`][`align_offset`] not failing
//! under certain circumstances. Specifically, [`align_offset`], when called in
//! a non-const context on a pointer to [`u8`], must succeed when the desired
//! alignment is less than or equal to the alignment of the allocation pointed
//! to by the provided pointer. In practice, this is true, even in [Miri] with
//! the `-Zmiri-symbolic-alignment-check` flag, but the specifications of
//! [`align_offset`] technically allow an implementation not to follow this
//! behavior. If you experience issues due to this, please file an issue in the
//! [Git repository]. As a workaround, you can enable the `fallback` feature,
//! which avoids relying on [`align_offset`] at the cost of making
//! [`TaggedPtr`] twice as large.
//!
//! [Miri]: https://github.com/rust-lang/miri
//!
//! Note that this crate is always sound: an implementation of [`align_offset`]
//! that doesn’t follow the required behavior may cause panics, but not
//! undefined behavior.
//!
//! [`align_offset`]:
//! https://doc.rust-lang.org/std/primitive.pointer.html#method.align_offset
//! [Git repository]: https://github.com/taylordotfish/tagged-pointer
//!
//! Unfortunately, there’s currently no way to implement space-efficient tagged
//! pointers in Rust without making some assumptions. However, this approach
//! has some advantages over the usual method of casting the pointer to a
//! [`usize`] and reusing the lower bits: the usual approach makes
//! platform-specific assumptions about the representation of pointers (which
//! currently apply to all platforms supported by rustc but could be
//! invalidated if support for new architectures is added, and there are
//! real architectures which do not allow reusing the lower bits of aligned
//! pointers), whereas this crate’s assumptions are platform-independent (aside
//! from the requirements already imposed by Rust, like having 8-bit bytes) and
//! are satisfied by all known implementations of Rust, including Miri with
//! `-Zmiri-symbolic-alignment-check`.

#[cfg(has_const_assert)]
macro_rules! const_assert {
    ($($tt:tt)*) => {
        ::core::assert!($($tt)*)
    };
}

/// NOTE: The assertions generated by this macro may be evaluated in code paths
/// that aren't taken. Therefore, `$cond` must contain *all* conditions
/// necessary and sufficient for the assertion to pass, independent of the flow
/// of code.
#[cfg(not(has_const_assert))]
macro_rules! const_assert {
    ($cond:expr $(,)?) => {
        const_assert!($cond, "assertion failed")
    };

    ($cond:expr, $msg:literal $(,)?) => {{
        let _ = [$msg][!$cond as usize];
    }};
}

/// Documentation for the const `BITS` parameter.
macro_rules! with_bits_doc {
    ($(#[$attr:meta])* pub $($tt:tt)+) => {
        $(#[$attr])*
        ///
        /// `BITS` specifies how many bits are used for the tag. The alignment
        /// of `T` must be large enough to store this many bits: if `BITS` is
        /// larger than the base-2 logarithm of the alignment of `T`[^bits],
        /// panics or compilation errors will occur.
        ///
        /// [^bits]: Equal to
        // Workaround for issues with links to Rust items in footnotes
        #[doc = "<code>\
            [align_of][core::mem::align_of]::\\<T>().\
            [ilog2][usize::ilog2]\\()\
            </code>,"]
        /// or, because alignment is always a power of 2,
        #[doc = "<code>\
            [align_of][core::mem::align_of]::\\<T>().\
            [trailing_zeros][usize::trailing_zeros]\\()\
            </code>."]
        pub $($tt)*
    };
}

mod ptr;
mod reference;
#[cfg(any(test, doctest))]
mod tests;

/// The type of the const `BITS` parameter. This could have been [`u32`], which
/// would match the `BITS` constants in primitive types (e.g., [`u8::BITS`]),
/// but [`usize`] is also suitable for storing any potential number of tag
/// bits: because the tag itself is stored in a [`usize`], it cannot possibly
/// consist of more than [`usize::MAX`] bits (or anywhere close to it).
type Bits = usize;

pub use ptr::TaggedPtr;
pub use reference::{TaggedMutRef, TaggedRef};

pub mod implied {
    pub use super::ptr::implied::*;
    pub use super::reference::implied::*;
}
