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

use super::messages;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;

#[repr(transparent)]
pub struct PtrImpl<T>(
    NonNull<u8>,
    PhantomData<NonNull<T>>,
);

impl<T> PtrImpl<T> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        let ptr = ptr.as_ptr().cast::<u8>();

        // Keep only the lower `BITS` bits of the tag.
        let tag = tag & Self::MASK;
        let offset = ptr.align_offset(Self::ALIGNMENT);
        assert!(offset != usize::MAX, "{}", messages::ALIGN_OFFSET_FAILED);

        // Check that none of the bits we're about to use are already set. If
        // `ptr` is aligned enough, we expect `offset` to be zero, but it could
        // theoretically be a nonzero multiple of `Self::ALIGNMENT`, so apply
        // the mask just in case.
        assert!(offset & Self::MASK == 0, "`ptr` is not aligned enough");
        let ptr = NonNull::new(ptr.wrapping_add(tag));
        Self(ptr.expect(messages::WRAPPED_TO_NULL), PhantomData)
    }

    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        let ptr = ptr.as_ptr().cast::<u8>().wrapping_add(tag);
        // SAFETY: We require from the caller that `ptr` is properly aligned
        // and that `tag <= Self::MASK`, therefore, since both the alignment of
        // `T` and `usize::MAX + 1` are a power of 2 adding `tag` cannot cross
        // the alignment boundary to the next object (and overflow to zero).
        // This combined with the fact that `ptr` came from a `NonNull<T>`,
        // means that the sum cannot be null.
        Self(unsafe { NonNull::new_unchecked(ptr) }, PhantomData)
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

    pub unsafe fn get_unchecked(self) -> (NonNull<T>, usize) {
        let ptr = self.0.as_ptr();
        let tag = ptr as usize & Self::MASK;
        let ptr = ptr.wrapping_sub(tag).cast::<T>();
        // SAFETY: We require that `self` was constructed with a properly
        // aligned `NonNull<T>` and with a `tag <= Self::MASK`, therefore after
        // subtracting `tag`, we get the original value of the `ptr` parameter,
        // which cannot be null because it was a `NonNull<T>`.
        (unsafe { NonNull::new_unchecked(ptr) }, tag)
    }
}

impl<T> Clone for PtrImpl<T> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}

impl<T> PartialEq for PtrImpl<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Ord for PtrImpl<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T> Hash for PtrImpl<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
