/*
 * Copyright 2021-2023 taylor.fish <contact@taylor.fish>
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

use super::Bits;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::ptr::NonNull;

pub(crate) struct PtrImpl<T, const BITS: Bits> {
    ptr: NonNull<T>,
    tag: usize,
}

impl<T, const BITS: Bits> PtrImpl<T, BITS> {
    pub(crate) fn new(ptr: NonNull<T>, tag: usize) -> Self {
        // Ensure compile-time checks are evaluated. Even though the checks
        // are not strictly necessary for the fallback implementation, it's
        // desirable to match the behavior of the standard implementation.
        Self::assert();
        Self {
            ptr,
            tag: tag & Self::MASK,
        }
    }

    pub(crate) unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self::new(ptr, tag)
    }

    pub(crate) fn get(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }

    pub(crate) unsafe fn get_unchecked(self) -> (NonNull<T>, usize) {
        self.get()
    }
}

impl<T, const BITS: Bits> Clone for PtrImpl<T, BITS> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            tag: self.tag,
        }
    }
}

impl<T, const BITS: Bits> PartialEq for PtrImpl<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        (self.ptr, self.tag) == (other.ptr, other.tag)
    }
}

impl<T, const BITS: Bits> Ord for PtrImpl<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.ptr, self.tag).cmp(&(other.ptr, other.tag))
    }
}

impl<T, const BITS: Bits> Hash for PtrImpl<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ptr, self.tag).hash(state);
    }
}
