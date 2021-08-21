/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * tagged-pointer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with tagged-pointer. If not, see <https://www.gnu.org/licenses/>.
 */

#![no_std]
#![warn(clippy::pedantic)]
#![allow(clippy::default_trait_access)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::non_ascii_literal)]

//! This crate provides an implementation of [tagged pointers]: pointers that
//! also contain an integer tag in a space-efficient manner.
//!
//! [tagged pointers]: https://en.wikipedia.org/wiki/Tagged_pointer
//!
//! Unless the fallback implementation is used (see the
//! [Assumptions](#assumptions) section below), both [`TaggedPtr`] and
//! [`Option<TaggedPtr>`] are guaranteed to be the size of a pointer.
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
//! use typenum::U2;
//!
//! #[repr(align(4))]
//! struct Item(u32, u32);
//!
//! # #[cfg(not(feature = "fallback"))]
//! # {
//! // `TaggedPtr` and `Option<TaggedPtr>` are both the size of a pointer:
//! assert_eq!(size_of::<TaggedPtr<Item, U2>>(), size_of::<usize>());
//! assert_eq!(size_of::<Option<TaggedPtr<Item, U2>>>(), size_of::<usize>());
//! # }
//!
//! let item1 = Item(1, 2);
//! let item2 = Item(3, 4);
//!
//! // We can store two bits of the tag, since `Item` has an alignment of 4.
//! let tp1 = TaggedPtr::<_, U2>::new(NonNull::from(&item1), 1);
//! let tp2 = TaggedPtr::<_, U2>::new(NonNull::from(&item2), 3);
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
//! under certain circumstances. Specifically, [`align_offset`], when called on
//! a pointer to [`u8`], must succeed when the desired alignment is less than
//! or equal to the alignment of the allocation pointed to by the provided
//! pointer. In practice, this is true, even in [Miri] with the
//! `-Zmiri-symbolic-alignment-check` flag, but the specifications of
//! [`align_offset`] technically allow an implementation not to follow this
//! behavior. If you experience issues due to this, please file an issue in the
//! [Git repository]. As a workaround, you can enable the `"fallback"` feature,
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
use typenum::Unsigned;

/// Calculates 2 to the power of [`Bits::USIZE`](Unsigned::USIZE), and panics
/// if the result wouldn't fit in a `usize`.
fn alignment<Bits: Unsigned>() -> usize {
    use core::convert::TryFrom;
    u32::try_from(Bits::USIZE)
        .ok()
        .and_then(|n| 1_usize.checked_shl(n))
        .expect("`Bits::USIZE` is too large")
}

/// Returns the bitmask that should be applied to the tag to ensure that it is
/// smaller than the alignment ([`alignment::<Bits>()`](alignment)). Since
/// the alignment is always a power of 2, this function simply subtracts 1
/// from the alignment.
fn mask<Bits: Unsigned>() -> usize {
    alignment::<Bits>() - 1
}

#[cfg_attr(feature = "fallback", path = "fallback.rs")]
mod ptr;
use ptr::PtrImpl;

#[cfg(test)]
mod tests;

impl<T, Bits> Copy for PtrImpl<T, Bits> {}

impl<T, Bits> Eq for PtrImpl<T, Bits> {}

impl<T, Bits> PartialOrd for PtrImpl<T, Bits> {
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
/// `Bits` should be a [type-level unsigned integer](Unsigned) from the
/// [typenum] crate. It specifies how many bits are used for the tag. The
/// alignment of `T` must be large enough to store this many bits; see
/// [`Self::new`].
#[repr(transparent)]
pub struct TaggedPtr<T, Bits>(PtrImpl<T, Bits>);

const BAD_TYPE_ALIGNMENT_MSG: &str = "\
alignment of `T` must be at least 2 to the power of `Bits::USIZE`";

impl<T, Bits: Unsigned> TaggedPtr<T, Bits> {
    /// Creates a new tagged pointer. Only the lower
    /// [`Bits::USIZE`](Unsigned::USIZE) bits of `tag` are stored.
    ///
    /// # Panics
    ///
    /// This function panics if the alignment of `T` is less than 2 to the
    /// power of [`Bits::USIZE`](Unsigned::USIZE). This ensures that all
    /// properly aligned pointers to `T` will be aligned enough to store the
    /// specified number of bits of the tag.
    ///
    /// `ptr` should be “dereferencable” in the sense defined by
    /// [`core::ptr`](core::ptr#safety). If it is not, this function or methods
    /// of [`TaggedPtr`] may panic.
    ///
    /// It is recommended that `ptr` be properly aligned (i.e., aligned to at
    /// least [`mem::align_of::<T>()`](mem::align_of)), but it may have a
    /// smaller alignment. However, if its alignment is not at least
    /// 2 to the power of [`Bits::USIZE`](Unsigned::USIZE), this function may
    /// panic.
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        // This should always be true.
        assert!(mem::align_of::<T>().is_power_of_two());
        assert!(
            mem::align_of::<T>().trailing_zeros() as usize >= Bits::USIZE,
            "{}",
            BAD_TYPE_ALIGNMENT_MSG,
        );
        // This should always be true.
        assert!(mem::size_of::<T>().max(1) >= mem::align_of::<T>());
        Self(PtrImpl::new(ptr, tag))
    }

    /// Gets the pointer and tag stored by the tagged pointer. If you need
    /// both the pointer and tag, this method may be more efficient than
    /// calling [`Self::ptr`] and [`Self::tag`] separately.
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferencable”](core::ptr#safety), this method may panic.
    pub fn get(self) -> (NonNull<T>, usize) {
        self.0.get()
    }

    /// Gets the pointer stored by the tagged pointer, without the tag.
    /// Equivalent to [`self.get().0`](Self::get).
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferencable”](core::ptr#safety), this method may panic.
    pub fn ptr(self) -> NonNull<T> {
        self.get().0
    }

    /// Gets the tag stored by the tagged pointer. Equivalent to
    /// [`self.get().1`](Self::get).
    ///
    /// # Panics
    ///
    /// If the pointer provided to [`Self::new`] wasn't
    /// [“dereferencable”](core::ptr#safety), this method may panic.
    pub fn tag(self) -> usize {
        self.get().1
    }
}

impl<T, Bits> Clone for TaggedPtr<T, Bits> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T, Bits> Copy for TaggedPtr<T, Bits> {}

impl<T, Bits> PartialEq for TaggedPtr<T, Bits> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, Bits> Eq for TaggedPtr<T, Bits> {}

impl<T, Bits> PartialOrd for TaggedPtr<T, Bits> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, Bits> Ord for TaggedPtr<T, Bits> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T, Bits> Hash for TaggedPtr<T, Bits> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T, Bits: Unsigned> fmt::Debug for TaggedPtr<T, Bits> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (ptr, tag) = self.get();
        f.debug_struct("TaggedPtr")
            .field("ptr", &ptr)
            .field("tag", &tag)
            .finish()
    }
}
