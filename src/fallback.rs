/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * tagged-pointer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with tagged-pointer. If not, see <https://www.gnu.org/licenses/>.
 */

use super::mask;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;
use typenum::Unsigned;

pub struct PtrImpl<T, Bits> {
    ptr: NonNull<T>,
    tag: usize,
    phantom: PhantomData<*const Bits>,
}

impl<T, Bits: Unsigned> PtrImpl<T, Bits> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self {
            ptr,
            tag: tag & mask::<Bits>(),
            phantom: PhantomData,
        }
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }
}

impl<T, Bits> Clone for PtrImpl<T, Bits> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            tag: self.tag,
            phantom: self.phantom,
        }
    }
}

impl<T, Bits> PartialEq for PtrImpl<T, Bits> {
    fn eq(&self, other: &Self) -> bool {
        (self.ptr, self.tag) == (other.ptr, other.tag)
    }
}

impl<T, Bits> Ord for PtrImpl<T, Bits> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.ptr, self.tag).cmp(&(other.ptr, other.tag))
    }
}

impl<T, Bits> Hash for PtrImpl<T, Bits> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ptr, self.tag).hash(state);
    }
}
