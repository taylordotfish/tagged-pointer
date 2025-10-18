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

use super::NumBits;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;

pub(super) struct PtrImpl<T, B = PhantomData<T>> {
    ptr: NonNull<T>,
    tag: usize,
    phantom: PhantomData<fn() -> B>,
}

impl<T, B: NumBits> PtrImpl<T, B> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        Self {
            ptr,
            tag: tag & Self::MASK,
            phantom: PhantomData,
        }
    }

    fn new_unchecked_impl(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        debug_assert!(tag < Self::ALIGNMENT);
        Self::new(ptr, tag)
    }

    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self::new_unchecked_impl(ptr, tag)
    }

    pub unsafe fn new_unchecked_dereferenceable(
        ptr: NonNull<T>,
        tag: usize,
    ) -> Self {
        Self::new_unchecked_impl(ptr, tag)
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        self.get_priv()
    }
}

impl<T, B> PtrImpl<T, B> {
    /// Private version of `get` that doesn't require `B: NumBits`.
    fn get_priv(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }
}

impl<T, B> PartialEq for PtrImpl<T, B> {
    fn eq(&self, other: &Self) -> bool {
        self.get_priv() == other.get_priv()
    }
}

impl<T, B> Ord for PtrImpl<T, B> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.get_priv().cmp(&other.get_priv())
    }
}

impl<T, B> Hash for PtrImpl<T, B> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_priv().hash(state);
    }
}
