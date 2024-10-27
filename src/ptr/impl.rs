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

use super::{NumBits, messages};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;

#[repr(transparent)]
pub struct PtrImpl<T, B = PhantomData<T>>(
    NonNull<u8>,
    #[allow(clippy::type_complexity)]
    PhantomData<(NonNull<T>, fn() -> B)>,
);

impl<T, B: NumBits> PtrImpl<T, B> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        let byte_ptr = ptr.as_ptr().cast::<u8>();
        let offset = byte_ptr.align_offset(Self::ALIGNMENT);
        assert!(offset != usize::MAX, "{}", messages::ALIGN_OFFSET_FAILED);
        // Check that none of the bits we're about to use are already set. If
        // `ptr` is aligned enough, we expect `offset` to be zero, but it could
        // theoretically be a nonzero multiple of `Self::ALIGNMENT`, so apply
        // the mask just in case.
        assert!(offset & Self::MASK == 0, "`ptr` is not aligned enough");
        // SAFETY: We just verified that `ptr` is suitably aligned, and `tag`
        // cannot exceed `Self::ALIGNMENT` after being masked.
        unsafe { Self::new_unchecked(ptr, tag & Self::MASK) }
    }

    /// # Safety
    ///
    /// * `ptr` must be aligned to at least [`Self::ALIGNMENT`] (if `ptr` is
    ///   properly aligned for its type, this requirement is automatically
    ///   fulfilled).
    /// * `tag` must be less than [`Self::ALIGNMENT`].
    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        debug_assert!(tag < Self::ALIGNMENT);
        let tagged = ptr.as_ptr().cast::<u8>().wrapping_add(tag);
        // SAFETY: Because `usize::MAX` is one less than a power of 2, `ptr`
        // (necessarily divisible by `Self::ALIGNMENT`) cannot be more than
        // `usize::MAX + 1 - Self::ALIGNMENT`. `tag` is strictly less than
        // `Self::ALIGNMENT`, so `tagged` cannot exceed `usize::MAX`; thus, it
        // cannot wrap to null.
        Self(unsafe { NonNull::new_unchecked(tagged) }, PhantomData)
    }

    /// # Safety
    ///
    /// All the conditions of [`Self::new_unchecked`] must be upheld, plus
    /// the first [`Self::ALIGNMENT`] bytes of `ptr` must be
    /// [dereferenceable](core::ptr#safety)
    pub unsafe fn new_unchecked_dereferenceable(
        ptr: NonNull<T>,
        tag: usize,
    ) -> Self {
        Self::assert();
        debug_assert!(tag < Self::ALIGNMENT);
        // SAFETY: Caller ensures this is within the bounds of the same
        // allocated object.
        let tagged = unsafe { ptr.as_ptr().cast::<u8>().add(tag) };
        // SAFETY: `pointer::add` cannot wrap to null if its safety conditions
        // are met.
        Self(unsafe { NonNull::new_unchecked(tagged) }, PhantomData)
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        let ptr = self.0.as_ptr();
        let offset = ptr.align_offset(Self::ALIGNMENT);
        assert!(offset != usize::MAX, "{}", messages::ALIGN_OFFSET_FAILED);

        // We expect that `offset < Self::ALIGNMENT`, but use `wrapping_sub`
        // just in case. Applying the mask is important both in the unlikely
        // case where `offset >= Self::ALIGNMENT`, and in the much more likely
        // case where `offset == 0`.
        let tag = Self::ALIGNMENT.wrapping_sub(offset) & Self::MASK;
        let ptr = ptr.wrapping_sub(tag).cast::<T>();
        debug_assert!(!ptr.is_null());

        // SAFETY: `self.0` was created by adding `tag` to the `ptr` parameter
        // in `Self::new`. After subtracting `tag`, we get the original value
        // of the `ptr` parameter, which cannot be null because it was a
        // `NonNull<T>`.
        (unsafe { NonNull::new_unchecked(ptr) }, tag)
    }
}

impl<T, B> PartialEq for PtrImpl<T, B> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, B> Ord for PtrImpl<T, B> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T, B> Hash for PtrImpl<T, B> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
