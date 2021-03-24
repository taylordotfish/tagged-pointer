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
use core::ptr::NonNull;

pub struct PtrImpl<T, const BITS: usize> {
    ptr: NonNull<T>,
    tag: usize,
}

impl<T, const BITS: usize> PtrImpl<T, BITS> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self {
            ptr,
            tag: tag & mask(BITS),
        }
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        (self.ptr, self.tag)
    }
}

impl<T, const BITS: usize> Clone for PtrImpl<T, BITS> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            tag: self.tag,
        }
    }
}

impl<T, const BITS: usize> PartialEq for PtrImpl<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        (self.ptr, self.tag) == (other.ptr, other.tag)
    }
}

impl<T, const BITS: usize> Ord for PtrImpl<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.ptr, self.tag).cmp(&(other.ptr, other.tag))
    }
}

impl<T, const BITS: usize> Hash for PtrImpl<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ptr, self.tag).hash(state);
    }
}
