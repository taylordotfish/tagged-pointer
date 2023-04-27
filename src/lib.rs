/*
 * Copyright 2021-2022 taylor.fish <contact@taylor.fish>
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

#![cfg_attr(not(test), no_std)]
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

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem;
use core::ptr::NonNull;

#[cfg(not(feature = "fallback"))]
mod messages;
#[cfg_attr(feature = "fallback", path = "fallback.rs")]
mod ptr;
use ptr::PtrImpl;

#[cfg(test)]
mod tests;

impl<T, const BITS: u32> PtrImpl<T, BITS> {
    /// Compile-time check of our assumption about the alignment of `T`. This
    /// should always succeed.
    const T_ALIGNED_PO2: () = assert!(
        mem::align_of::<T>().is_power_of_two(),
        "unexpected alignment of `T`"
    );
    /// Compile-time check of our assumption about the size vs alignment of
    /// `T`. This should always succeed.
    const T_SIZE_GE_ALIGNMENT: () = assert!(
        mem::size_of::<T>() == 0
            || mem::size_of::<T>() >= mem::align_of::<T>(),
        "unexpected `size_of` vs `align_of` for `T`"
    );
    /// Compile-time check that the requested `BITS` is small enough.
    const ENOUGH_ALIGNMENT_BITS: () = assert!(
        mem::align_of::<T>().trailing_zeros() >= BITS,
        "alignment of `T` must be greater or equal to `BITS`"
    );

    /// Calculates 2 to the power of `BITS`, and panics if the result wouldn't
    /// fit in a `usize`. This is the alignment required to store `BITS`
    /// tag bits.
    const ALIGNMENT: usize = if let Some(align) = 1_usize.checked_shl(BITS) {
        align
    } else {
        panic!("2 to the power of `BITS` does not fit in a `usize`")
    };

    /// The bitmask that should be applied to the tag to ensure that it
    /// is smaller than [`Self::ALIGNMENT`].
    /// Since the alignment is always a power of 2, this simply
    /// subtracts 1 from the alignment.
    const MASK: usize = Self::ALIGNMENT - 1;
}

impl<T, const BITS: u32> Copy for PtrImpl<T, BITS> {}

impl<T, const BITS: u32> Eq for PtrImpl<T, BITS> {}

impl<T, const BITS: u32> PartialOrd for PtrImpl<T, BITS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A tagged pointer: a space-efficient representation of a pointer and integer
/// tag.
///
/// This type stores a pointer and an integer tag without taking up more
/// space than a normal pointer (unless the fallback implementation is used;
/// see the [crate documentation](crate#assumptions)).
///
/// The tagged pointer conceptually holds a [`NonNull<T>`](NonNull) and a
/// certain number of bits of an integer tag.
///
/// `BITS` specifies how many bits are used for the tag. The alignment of `T`
/// must be large enough to store this many bits; see [`Self::new`].
#[repr(transparent)]
pub struct TaggedPtr<T, const BITS: u32>(PtrImpl<T, BITS>);

impl<T, const BITS: u32> TaggedPtr<T, BITS> {
    /// Creates a new tagged pointer. Only the lower `BITS` bits of `tag` are
    /// stored. A check is performed at compile time that the alignment of `T`
    /// is not less than 2<sup>`BITS`</sup> (`1 << BITS`). This ensures that
    /// all properly aligned pointers to `T` will be aligned enough to store
    /// the specified number of bits of the tag.
    ///
    /// # Panics
    ///
    /// `ptr` should be “dereferenceable” in the sense defined by
    /// [`core::ptr`](core::ptr#safety).[^1] If it is not, this function or
    /// methods of [`TaggedPtr`] may panic.
    ///
    /// It is recommended that `ptr` be properly aligned (i.e., aligned to at
    /// least [`mem::align_of::<T>()`](mem::align_of)), but it may have a
    /// smaller alignment. However, if its alignment is not at least
    /// 2<sup>`BITS`</sup>, this function may panic.
    ///
    /// [^1]: It is permissible for only the first 2<sup>`BITS`</sup> bytes of
    /// `ptr` to be dereferenceable.
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self(PtrImpl::new(ptr, tag))
    }

    /// Gets the pointer and tag stored by the tagged pointer. If you need
    /// both the pointer and tag, this method may be more efficient than
    /// calling [`Self::ptr`] and [`Self::tag`] separately.
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferenceable”](core::ptr#safety), this method may panic.
    pub fn get(self) -> (NonNull<T>, usize) {
        self.0.get()
    }

    /// Gets the pointer stored by the tagged pointer, without the tag.
    /// Equivalent to [`self.get().0`](Self::get).
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferenceable”](core::ptr#safety), this method may panic.
    pub fn ptr(self) -> NonNull<T> {
        self.get().0
    }

    /// Sets the pointer without modifying the tag.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use {core::ptr::NonNull, tagged_pointer::TaggedPtr};
    /// # trait Ext<T> { fn set_ptr(&mut self, ptr: NonNull<T>); }
    /// # impl<T, const BITS: u32> Ext<T> for TaggedPtr<T, BITS> {
    /// # fn set_ptr(&mut self, ptr: NonNull<T>) {
    /// *self = Self::new(ptr, self.tag());
    /// # }}
    /// ```
    ///
    /// # Panics
    ///
    /// See [`Self::new`].
    pub fn set_ptr(&mut self, ptr: NonNull<T>) {
        *self = Self::new(ptr, self.tag());
    }

    /// Gets the tag stored by the tagged pointer. Equivalent to
    /// [`self.get().1`](Self::get).
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferenceable”](core::ptr#safety), this method may panic.
    pub fn tag(self) -> usize {
        self.get().1
    }

    /// Sets the tag without modifying the pointer.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedPtr;
    /// # trait Ext { fn set_tag(&mut self, tag: usize); }
    /// # impl<T, const BITS: u32> Ext for TaggedPtr<T, BITS> {
    /// # fn set_tag(&mut self, tag: usize) {
    /// *self = Self::new(self.ptr(), tag);
    /// # }}
    /// ```
    ///
    /// # Panics
    ///
    /// See [`Self::new`].
    pub fn set_tag(&mut self, tag: usize) {
        *self = Self::new(self.ptr(), tag);
    }
}

impl<T, const BITS: u32> Clone for TaggedPtr<T, BITS> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T, const BITS: u32> Copy for TaggedPtr<T, BITS> {}

impl<T, const BITS: u32> PartialEq for TaggedPtr<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, const BITS: u32> Eq for TaggedPtr<T, BITS> {}

impl<T, const BITS: u32> PartialOrd for TaggedPtr<T, BITS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, const BITS: u32> Ord for TaggedPtr<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T, const BITS: u32> Hash for TaggedPtr<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T, const BITS: u32> fmt::Debug for TaggedPtr<T, BITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (ptr, tag) = self.get();
        f.debug_struct("TaggedPtr")
            .field("ptr", &ptr)
            .field("tag", &tag)
            .finish()
    }
}
