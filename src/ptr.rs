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

use super::messages;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;

#[repr(transparent)]
pub struct PtrImpl<T, const BITS: u32>(NonNull<u8>, PhantomData<NonNull<T>>);

impl<T, const BITS: u32> PtrImpl<T, BITS> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        // Compile-time checks.
        let _ = Self::T_ALIGNED_PO2;
        let _ = Self::T_SIZE_GE_ALIGNMENT;
        let _ = Self::ENOUGH_ALIGNMENT_BITS;
        let ptr = ptr.as_ptr().cast::<u8>();
        // Keep only the lower `BITS` bits of the tag.
        let tag = tag & Self::MASK;
        let offset = ptr.align_offset(Self::ALIGNMENT);
        assert!(offset != usize::MAX, "{}", messages::ALIGN_OFFSET_FAILED);
        // Check that none of the bits we're about to use are already set.
        // We expect that `offset <= Self::MASK` but do the `&` just in case.
        assert!(offset & Self::MASK == 0, "`ptr` is not aligned enough");
        Self(
            NonNull::new(ptr.wrapping_add(tag))
                .expect(messages::WRAPPED_TO_NULL),
            PhantomData,
        )
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        let ptr = self.0.as_ptr();
        let offset = ptr.align_offset(Self::ALIGNMENT);
        assert!(offset != usize::MAX, "{}", messages::ALIGN_OFFSET_FAILED);
        // We expect that `offset <= Self::MASK` but do the `&` just in case.
        let tag = (Self::ALIGNMENT - offset) & Self::MASK;
        let ptr = ptr.wrapping_sub(tag).cast::<T>();
        debug_assert!(!ptr.is_null());
        // SAFETY: `self.0` was created by adding `tag` to the `ptr` parameter
        // in `Self::new`. After subtracting `tag`, we get the original value
        // of the `ptr` parameter, which cannot be null because it was a
        // `NonNull<T>`.
        (unsafe { NonNull::new_unchecked(ptr) }, tag)
    }
}

impl<T, const BITS: u32> Clone for PtrImpl<T, BITS> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}

impl<T, const BITS: u32> PartialEq for PtrImpl<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, const BITS: u32> Ord for PtrImpl<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T, const BITS: u32> Hash for PtrImpl<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
