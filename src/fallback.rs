/*
 * Copyright 2021 taylor.fish <contact@taylor.fish>
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

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::ptr::NonNull;

pub struct PtrImpl<T, const BITS: u32> {
    ptr: NonNull<T>,
    tag: usize,
}

impl<T, const BITS: u32> PtrImpl<T, BITS> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        // Even though these checks are not necessary here, we want to ensure
        // that if the fallback compiles then so would the default.
        let _ = Self::T_ALIGNED_PO2;
        let _ = Self::T_SIZE_GE_ALIGNMENT;
        let _ = Self::ENOUGH_ALIGNMENT_BITS;
        Self {
            ptr,
            tag: tag & Self::MASK,
        }
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }
}

impl<T, const BITS: u32> Clone for PtrImpl<T, BITS> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            tag: self.tag,
        }
    }
}

impl<T, const BITS: u32> PartialEq for PtrImpl<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        (self.ptr, self.tag) == (other.ptr, other.tag)
    }
}

impl<T, const BITS: u32> Ord for PtrImpl<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.ptr, self.tag).cmp(&(other.ptr, other.tag))
    }
}

impl<T, const BITS: u32> Hash for PtrImpl<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ptr, self.tag).hash(state);
    }
}
