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

use super::{alignment, mask};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr::NonNull;

const WRAPPED_TO_NULL_MSG: &str = "\
`ptr` became null after adding `tag`. This shouldn't happen if `ptr` is
“dereferencable” in the sense defined by `std::ptr`.";

const ALIGN_OFFSET_FAILED_MSG: &str = "\
Error: `align_offset` failed. This is due to one of the following reasons:

* The pointer passed to `TaggedPtr::new` wasn't “dereferencable” in the sense
  defined by the documentation for `std::ptr`. (This is the most likely cause.)

* The current implementation of `align_offset` sometimes or always fails, even
  when the desired alignment is less than or equal to the alignment of the
  allocation pointed to by the provided pointer. This shouldn't happen in
  practice, even in Miri with `-Zmiri-symbolic-alignment-check`, but is
  technically allowed. If this happens, please file an issue at
  <https://github.com/taylordotfish/tagged-pointer>. As a workaround, enable
  the `\"fallback\"` feature in the “tagged-pointer” crate. This avoids relying
  on `align_offset` at the cost of using twice as much memory.";

#[repr(transparent)]
pub struct PtrImpl<T, const BITS: usize>(NonNull<u8>, PhantomData<NonNull<T>>);

impl<T, const BITS: usize> PtrImpl<T, BITS> {
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        let ptr = ptr.as_ptr();
        // Keep only the lower `BITS` bits of the tag.
        let tag = tag & mask(BITS);
        match ptr.align_offset(alignment(BITS)) {
            0 => Self(
                NonNull::new(ptr.cast::<u8>().wrapping_add(tag))
                    .expect(WRAPPED_TO_NULL_MSG),
                PhantomData,
            ),
            usize::MAX => panic!("{}", ALIGN_OFFSET_FAILED_MSG),
            _ => panic!("`ptr` is not aligned enough"),
        }
    }

    pub fn get(self) -> (NonNull<T>, usize) {
        let ptr = self.0.as_ptr();
        let offset = ptr.align_offset(alignment(BITS));
        assert!(offset != usize::MAX, "{}", ALIGN_OFFSET_FAILED_MSG);
        let tag = alignment(BITS).wrapping_sub(offset) & mask(BITS);
        let ptr = ptr.wrapping_sub(tag).cast::<T>();
        debug_assert!(!ptr.is_null());
        // SAFETY: `self.0` was created by adding `tag` to the `ptr` parameter
        // in `Self::new`. After subtracting `tag`, we get the original value
        // of the `ptr` parameter, which cannot be null because it was a
        // `NonNull<T>`.
        (unsafe { NonNull::new_unchecked(ptr) }, tag)
    }
}

impl<T, const BITS: usize> Clone for PtrImpl<T, BITS> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}

impl<T, const BITS: usize> PartialEq for PtrImpl<T, BITS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, const BITS: usize> Ord for PtrImpl<T, BITS> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T, const BITS: usize> Hash for PtrImpl<T, BITS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
