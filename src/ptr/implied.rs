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

#[cfg(doc)]
use core::mem;
use core::ptr::NonNull;
use super::ptr_impl::PtrImpl;

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
    /// The number of bits that this tagged pointer can store. Equal to
    /// <code>[mem::align_of]::\<T>().[trailing_zeros]()</code> (the base-2
    /// logarithm of the alignment of `T`).
    ///
    /// [trailing_zeros]: usize::trailing_zeros
    pub const BITS: u32 = PtrImpl::<T>::BITS;

    /// The maximum tag (inclusive) that this tagged pointer can store. Equal
    /// to <code>[mem::align_of]::\<T>() - 1</code>.
    pub const MAX_TAG: usize = PtrImpl::<T>::MASK;

    /// Creates a new tagged pointer. Only the lower [`Self::BITS`] bits of
    /// `tag` are stored.
    ///
    /// `ptr` should be “dereferenceable” in the sense defined by
    /// [`core::ptr`](core::ptr#safety). Otherwise, the pointers returned by
    /// [`Self::get`] and [`Self::ptr`] may not be equivalent to `ptr`---it may
    /// be unsound to use them in ways that are sound for `ptr`.
    ///
    /// # Panics
    ///
    /// This function may panic if `ptr` is not properly aligned (i.e., aligned
    /// to at least [`mem::align_of::<T>()`]).
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self(PtrImpl::new(ptr, tag))
    }

    /// Creates a new tagged pointer.
    ///
    /// Equivalent to [`Self::new`] but without some runtime checks. The
    /// comments about `ptr` being “dereferenceable” also apply to this
    /// function.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned (i.e., aligned to at least
    ///   [`mem::align_of::<T>()`]).
    /// * `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { PtrImpl::new_unchecked(ptr, tag) })
    }
}

impl_tagged_ptr_common!(
    [T],
    [T],
    "# use tagged_pointer::implied::TaggedPtr;",
);
