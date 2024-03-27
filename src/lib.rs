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

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem;
use core::ptr::NonNull;

#[cfg(not(feature = "fallback"))]
mod messages;
#[cfg_attr(feature = "fallback", path = "fallback.rs")]
mod ptr;
mod r#ref;
use ptr::PtrImpl;
pub use r#ref::{TaggedMutRef, TaggedRef};

#[cfg(any(test, doctest))]
mod tests;

/// see, e.g., [`u32::BITS`].
type Bits = u32;

struct Check<T, const BITS: Bits>(T);
impl<T, const BITS: Bits> Check<T, BITS> {
    #[allow(clippy::no_effect)]
    /// Compile-time checks. Referencing this with `let _ = Check::<T, BITS>::ASSERT;`
    /// ensures that the compile time checks are run. See e.g. [`TaggedPtr::new`].
    const ASSERT: () = {
        // The `BITS` constant was correctly provided to `new`.
        let b = BITS == Self::BITS;
        match Self::BITS {
            0 => ["`BITS` must be equal to 0"][!b as usize],
            1 => ["`BITS` must be equal to 1"][!b as usize],
            2 => ["`BITS` must be equal to 2"][!b as usize],
            3 => ["`BITS` must be equal to 3"][!b as usize],
            4 => ["`BITS` must be equal to 4"][!b as usize],
            5 => ["`BITS` must be equal to 5"][!b as usize],
            6 => ["`BITS` must be equal to 6"][!b as usize],
            7 => ["`BITS` must be equal to 7"][!b as usize],
            8 => ["`BITS` must be equal to 8"][!b as usize],
            9 => ["`BITS` must be equal to 9"][!b as usize],
            10 => ["`BITS` must be equal to 10"][!b as usize],
            11 => ["`BITS` must be equal to 11"][!b as usize],
            12 => ["`BITS` must be equal to 12"][!b as usize],
            13 => ["`BITS` must be equal to 13"][!b as usize],
            14 => ["`BITS` must be equal to 14"][!b as usize],
            15 => ["`BITS` must be equal to 15"][!b as usize],
            16 => ["`BITS` must be equal to 16"][!b as usize],
            _ => ["`BITS` must be equal to `mem::align_of::<T>().trailing_zeros()`"][!b as usize],
        };

        // Assumption about the alignment of `T`. This should always succeed.
        let b = mem::align_of::<T>().is_power_of_two();
        ["expected alignment of `T` to be a power of 2"][!b as usize];

        // Assumption about the size of `T`. This should always succeed.
        let b = match mem::size_of::<T>() {
            0 => true,
            n => n >= mem::align_of::<T>(),
        };
        ["expected size of non-ZST `T` to be at least alignment"][!b as usize];

        // Assumption about the size of `T`. This should always succeed.
        let b = mem::size_of::<T>() % mem::align_of::<T>() == 0;
        ["expected size of `T` to be multiple of alignment"][!b as usize];

        // Ensure `1 << BITS` doesn't overflow.
        let b = 1_usize.checked_shl(Self::BITS).is_some();
        ["`1 << BITS` doesn't fit in a `usize`"][!b as usize];

        // Ensure `T` is aligned enough to store `BITS` bits. This will always
        // succeed, but is kept around in case `PtrImpl::<T>::BITS` changes.
        let b = mem::align_of::<T>().trailing_zeros() >= Self::BITS;
        ["alignment of `T` must be at least `1 << BITS`"][!b as usize];
    };

    const BITS: u32 = PtrImpl::<T>::BITS;
}

impl<T> PtrImpl<T> {
    const BITS: u32 = mem::align_of::<T>().trailing_zeros();

    /// The alignment required to store `BITS` tag bits. We ensured this
    /// doesn't overflow earlier, so use `wrapping_shl` so that we get only
    /// one compiler error.
    const ALIGNMENT: usize = 1_usize.wrapping_shl(Self::BITS);

    /// The bitmask that should be applied to the tag to ensure that it is
    /// smaller than [`Self::ALIGNMENT`]. Since the alignment is always a power
    /// of 2, simply subtract 1 from the alignment.
    const MASK: usize = Self::ALIGNMENT - 1;
}

impl<T> Copy for PtrImpl<T> {}

impl<T> Eq for PtrImpl<T> {}

impl<T> PartialOrd for PtrImpl<T> {
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
/// The number of bits that can be stored in the tag is determined as
/// `mem::align_of::<T>().trailing_zeros()`, any higher bits in the tag will
/// be masked away. See [`Self::new`] for more details.
#[repr(transparent)]
pub struct TaggedPtr<T>(PtrImpl<T>);

impl<T> TaggedPtr<T> {
    /// Creates a new tagged pointer. Only the lower `BITS` bits of `tag` are
    /// stored.
    ///
    /// A check is performed at compile time to ensure that the alignment of
    /// `T` is exactly 2<sup>`BITS`</sup> (i.e. that `BITS ==
    /// mem::align_of::<T>().trailing_zeros()`). This ensures
    /// that all properly aligned pointers to `T` will be aligned enough to
    /// store the specified number of bits of the tag.
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
    pub fn new<const BITS: Bits>(ptr: NonNull<T>, tag: usize) -> Self {
        // Perform compile-time checks as close to call site so that
        // diagnostics point to user code.
        let _ = Check::<T, BITS>::ASSERT;
        Self::new_implied(ptr, tag)
    }

    /// Creates a new tagged pointer. Identical to [`Self::new`] but without
    /// needing to explicitly specify the expected number of available bits.
    /// The number of bits is determined as `mem::align_of::<T>().trailing_zeros()`.
    /// 
    /// Using this method is generally not recommended since the tag may be
    /// unexpectedly truncated if the alignment of `T` is not what you expect.
    pub fn new_implied(ptr: NonNull<T>, tag: usize) -> Self {
        Self(PtrImpl::new(ptr, tag))
    }

    /// Creates a new tagged pointer.
    ///
    /// A check is performed at compile time to ensure that the alignment of
    /// `T` is exactly 2<sup>`BITS`</sup> (i.e. that `BITS ==
    /// mem::align_of::<T>().trailing_zeros()`). This ensures
    /// that all properly aligned pointers to `T` will be aligned enough to
    /// store the specified number of bits of the tag.
    ///
    /// # Safety
    ///
    /// `ptr` must be properly aligned.
    ///
    /// `tag` must not be larger than [`Self::mask`].
    pub unsafe fn new_unchecked<const BITS: Bits>(ptr: NonNull<T>, tag: usize) -> Self {
        // Perform compile-time checks as close to call site so that
        // diagnostics point to user code.
        let _ = Check::<T, BITS>::ASSERT;
        unsafe { Self::new_implied_unchecked(ptr, tag) }
    }

    /// Creates a new tagged pointer. Identical to [`Self::new_unchecked`] but without
    /// needing to explicitly specify the expected number of available bits.
    /// The number of bits is determined as `mem::align_of::<T>().trailing_zeros()`.
    /// 
    /// Using this method is generally not recommended since the tag may be
    /// unexpectedly truncated if the alignment of `T` is not what you expect.
    pub unsafe fn new_implied_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self(unsafe { PtrImpl::new_unchecked(ptr, tag) })
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

    /// Gets the (properly aligned) pointer and tag stored by the tagged
    /// pointer.
    ///
    /// # Safety
    ///
    /// `self` must have been constructed with a `ptr` and `tag` which uphold
    /// the safety criteria set out in [`Self::new_unchecked`]. Note that
    /// [`Self::new`] internally masks its `tag` argument, and so only the
    /// `ptr` restriction applies in that case.
    pub unsafe fn get_unchecked(self) -> (NonNull<T>, usize) {
        unsafe { self.0.get_unchecked() }
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
    /// # impl<T> Ext<T> for TaggedPtr<T> {
    /// # fn set_ptr(&mut self, ptr: NonNull<T>) {
    /// *self = Self::new_implied(ptr, self.tag());
    /// # }}
    /// ```
    ///
    /// # Panics
    ///
    /// See [`Self::new`].
    pub fn set_ptr(&mut self, ptr: NonNull<T>) {
        *self = Self::new_implied(ptr, self.tag());
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
    /// # trait Ext { fn set_tag<const BITS: u32>(&mut self, tag: usize); }
    /// # impl<T> Ext for TaggedPtr<T> {
    /// # fn set_tag<const BITS: u32>(&mut self, tag: usize) {
    /// *self = Self::new::<BITS>(self.ptr(), tag);
    /// # }}
    /// ```
    ///
    /// # Panics
    ///
    /// See [`Self::new`].
    pub fn set_tag<const BITS: Bits>(&mut self, tag: usize) {
        // Perform compile-time checks as close to call site so that
        // diagnostics point to user code.
        let _ = Check::<T, BITS>::ASSERT;
        *self = Self::new_implied(self.ptr(), tag);
    }

    /// Returns the bitmask for the tag, use `tag & TaggedPtr::mask()` to
    /// ensure safety of [`Self::new_unchecked`]. Calculated as
    /// 2<sup>`BITS`</sup> - 1.
    pub const fn mask() -> usize {
        PtrImpl::<T>::MASK
    }
}

impl<T> Clone for TaggedPtr<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T> Copy for TaggedPtr<T> {}

impl<T> PartialEq for TaggedPtr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for TaggedPtr<T> {}

impl<T> PartialOrd for TaggedPtr<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for TaggedPtr<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T> Hash for TaggedPtr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> fmt::Debug for TaggedPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (ptr, tag) = self.get();
        f.debug_struct("TaggedPtr")
            .field("ptr", &ptr)
            .field("tag", &tag)
            .finish()
    }
}
