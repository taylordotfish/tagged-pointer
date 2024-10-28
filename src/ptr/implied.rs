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

use super::PtrImpl;
use core::ptr::NonNull;

/// A tagged pointer with the maximum tag size for the given type.
///
/// This type behaves like [`crate::TaggedPtr`] but doesn't have a `BITS`
/// parameter that determines how many tag bits to store. Instead, this type
/// uses the largest possible tag size for an *aligned* pointer to `T`; see
/// [`Self::BITS`] for the exact calculation.
///
/// Unlike [`crate::TaggedPtr`], this type always requires pointers to be
/// properly aligned, even if you don't need all the available tag bits;
/// see [`Self::new`].
#[repr(transparent)]
pub struct TaggedPtr<T>(PtrImpl<T>);

impl<T> TaggedPtr<T> {
    /// The number of tag bits that this tagged pointer can store. Equal to
    /// <code>[align_of]::\<T>().[trailing_zeros]\()</code> (because alignment
    /// is always a power of 2, this is the base-2 logarithm of the alignment
    /// of `T`).
    ///
    /// [align_of]: core::mem::align_of
    /// [trailing_zeros]: usize::trailing_zeros
    pub const BITS: u32 = Self::bits();

    // Separate function so Rustdoc doesn't show the expression
    const fn bits() -> u32 {
        PtrImpl::<T>::BITS
    }

    /// The maximum tag (inclusive) that this tagged pointer can store. Equal
    /// to <code>[align_of]::\<T>() - 1</code>.
    ///
    /// [align_of]: core::mem::align_of
    pub const MAX_TAG: usize = Self::max_tag();

    // Separate function so Rustdoc doesn't show the expression
    const fn max_tag() -> usize {
        PtrImpl::<T>::MASK
    }

    /// Creates a new tagged pointer. Only the lower [`Self::BITS`] bits of
    /// `tag` are stored.
    ///
    /// `ptr` should be "dereferenceable" in the sense defined by
    /// [`core::ptr`](core::ptr#safety). Otherwise, the pointers returned by
    /// [`Self::get`] and [`Self::ptr`] may not be equivalent to `ptr`---it may
    /// be unsound to use them in ways that are sound for `ptr`.
    ///
    /// # Panics
    ///
    /// This function may panic if `ptr` is not properly aligned (i.e., aligned
    /// to at least [`align_of::<T>()`][core::mem::align_of]).
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self(PtrImpl::new(ptr, tag))
    }

    /// Creates a new tagged pointer.
    ///
    /// Equivalent to [`Self::new`] but without some runtime checks. The
    /// comments about `ptr` being "dereferenceable" also apply to this
    /// function.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned (i.e., aligned to at least
    ///   [`align_of::<T>()`][core::mem::align_of]).
    /// * `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { PtrImpl::new_unchecked(ptr, tag) })
    }

    /// Like [`Self::new_unchecked`], but the pointer must be dereferenceable,
    /// which allows better optimization.
    ///
    /// # Safety
    ///
    /// All conditions of [`Self::new_unchecked`] must be upheld, plus `ptr`
    /// must be "dereferenceable" in the sense defined by
    /// [`core::ptr`](core::ptr#safety).
    pub unsafe fn new_unchecked_dereferenceable(
        ptr: NonNull<T>,
        tag: usize,
    ) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { PtrImpl::new_unchecked_dereferenceable(ptr, tag) })
    }
}

impl_tagged_ptr_common!([T], [T], "# use tagged_pointer::implied::TaggedPtr;");
