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
use core::ptr::NonNull;
use core::marker::PhantomData;

pub struct PtrImpl<T, B = PhantomData<T>> {
    ptr: NonNull<T>,
    tag: usize,
}

impl<T, B: NumBits> PtrImpl<T, B> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        Self {
            ptr,
            tag: tag & Self::MASK,
        }
    }

    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        Self::assert();
        debug_assert!(tag < Self::ALIGNMENT);
        Self::new(ptr, tag)
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }
}

impl<T> PartialEq for PtrImpl<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T> Ord for PtrImpl<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.get().cmp(&other.get())
    }
}

impl<T> Hash for PtrImpl<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}
