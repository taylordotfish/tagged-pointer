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

use core::cmp::Ordering;
use core::mem;
use core::ptr::NonNull;
use core::marker::PhantomData;
use super::Bits;

#[cfg_attr(feature = "fallback", allow(dead_code))]
mod messages;
mod ptr_impl;
use ptr_impl::PtrImpl;

trait NumBits {
    const BITS: u32;
}

impl<T> NumBits for PhantomData<T> {
    const BITS: u32 = mem::align_of::<T>().trailing_zeros();
}

struct ConstBits<const N: u32>;

impl<const N: u32> NumBits for ConstBits<N> {
    const BITS: u32 = N;
}

impl<T, B: NumBits> PtrImpl<T, B> {
    /// The number of tag bits that can be stored.
    pub const BITS: u32 = B::BITS;

    /// The alignment required to store [`Self::BITS`] tag bits. Separate
    /// compile-time checks ensure this value doesn't overflow.
    pub const ALIGNMENT: usize = 1_usize.wrapping_shl(Self::BITS);

    /// The bitmask that should be applied to the tag to ensure that it is
    /// smaller than [`Self::ALIGNMENT`]. Since the alignment is always a power
    /// of 2, simply subtract 1 from the alignment.
    pub const MASK: usize = Self::ALIGNMENT - 1;

    const ASSERT: bool = {
        let bits = Self::BITS;
        let size = mem::size_of::<T>();
        let align = mem::align_of::<T>();
        let tz = mem::align_of::<T>().trailing_zeros();
        // Ensure `BITS` isn't too large.
        const_assert!(tz != 0 || bits == 0, "`BITS` must be 0 (alignment of T is 1)");
        const_assert!(tz != 1 || bits <= 1, "`BITS` must be <= 1 (alignment of T is 2)");
        const_assert!(tz != 2 || bits <= 2, "`BITS` must be <= 2 (alignment of T is 4)");
        const_assert!(tz != 3 || bits <= 3, "`BITS` must be <= 3 (alignment of T is 8)");
        const_assert!(tz != 4 || bits <= 4, "`BITS` must be <= 4 (alignment of T is 16)");
        const_assert!(tz != 5 || bits <= 5, "`BITS` must be <= 5 (alignment of T is 32)");
        const_assert!(tz != 6 || bits <= 6, "`BITS` must be <= 6 (alignment of T is 64)");
        const_assert!(tz != 7 || bits <= 7, "`BITS` must be <= 7 (alignment of T is 128)");
        const_assert!(tz != 8 || bits <= 8, "`BITS` must be <= 8 (alignment of T is 256)");
        const_assert!(bits <= tz, "`BITS` cannot exceed align_of::<T>().trailing_zeros()");
        // Ensure `1 << BITS` doesn't overflow.
        const_assert!(1_usize.checked_shl(bits).is_some(), "`BITS` must be less than number of bits in `usize`");
        // Assumption about the alignment of `T`. This should always succeed.
        const_assert!(align.is_power_of_two());
        // Assumption about the size of `T`. This should always succeed.
        const_assert!(size == 0 || size >= align);
        // Assumption about the size of `T`. This should always succeed.
        const_assert!(size % align == 0, "expected size of `T` to be a multiple of alignment");
        true
    };

    /// Compile-time checks.
    fn assert() {
        // This run-time assertion will always succeed (and will likely be
        // optimized out), but makes it clear that we need the constant to be
        // evaluated (this type's soundness relies on its validity).
        assert!(Self::ASSERT);
    }

    pub fn ptr(self) -> NonNull<T> {
        self.get().0
    }

    pub fn set_ptr(&mut self, ptr: NonNull<T>) {
        *self = Self::new(ptr, self.tag());
    }

    pub fn tag(self) -> usize {
        self.get().1
    }

    pub fn set_tag(&mut self, tag: usize) {
        *self = Self::new(self.ptr(), tag);
    }
}

impl<T, B> Copy for PtrImpl<T, B> {}

impl<T, B> Clone for PtrImpl<T, B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, B> Eq for PtrImpl<T, B> {}

impl<T, B> PartialOrd for PtrImpl<T, B> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! impl_tagged_ptr_common {
    (
        [$($ty_params:tt)*],
        $ty:ty,
        $name_str:literal,
        $doctest_context:literal $(,)?
    ) => { const _: () = {
        use core::cmp::Ordering;
        use core::fmt;
        use core::hash::{Hash, Hasher};
        use core::ptr::NonNull;

        impl<$($ty_params)*> $ty {
            /// Gets the pointer and tag stored by the tagged pointer. If you
            /// need both the pointer and tag, this method may be more
            /// efficient than calling [`Self::ptr`] and [`Self::tag`]
            /// separately.
            pub fn get(self) -> (NonNull<T>, usize) {
                self.0.get()
            }

            /// Gets the pointer stored by the tagged pointer, without the tag.
            /// Equivalent to [`self.get().0`](Self::get).
            pub fn ptr(self) -> NonNull<T> {
                self.0.ptr()
            }

            /// Sets the pointer without modifying the tag.
            ///
            /// This method is simply equivalent to:
            ///
            /// ```
            /// # use core::ptr::NonNull;
            /// # trait Ext<T> { fn set_ptr(&mut self, ptr: NonNull<T>); }
            #[doc = $doctest_context]
            /// # { fn set_ptr(&mut self, ptr: NonNull<T>) {
            /// *self = Self::new(ptr, self.tag());
            /// # }}
            /// ```
            ///
            /// See [`Self::new`] for information on argument validity and
            /// panics.
            pub fn set_ptr(&mut self, ptr: NonNull<T>) {
                self.0.set_ptr(ptr)
            }

            /// Gets the tag stored by the tagged pointer. Equivalent to
            /// [`self.get().1`](Self::get).
            pub fn tag(self) -> usize {
                self.0.tag()
            }

            /// Sets the tag without modifying the pointer.
            ///
            /// This method is simply equivalent to:
            ///
            /// ```
            /// # trait Ext { fn set_tag(&mut self, tag: usize); }
            #[doc = $doctest_context]
            /// # { fn set_tag(&mut self, tag: usize) {
            /// *self = Self::new(self.ptr(), tag);
            /// # }}
            /// ```
            ///
            /// See [`Self::new`] for more information.
            pub fn set_tag(&mut self, tag: usize) {
                self.0.set_tag(tag)
            }
        }

        impl<$($ty_params)*> Clone for $ty {
            fn clone(&self) -> Self {
                Self(self.0)
            }
        }

        impl<$($ty_params)*> Copy for $ty {}

        impl<$($ty_params)*> PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl<$($ty_params)*> Eq for $ty {}

        impl<$($ty_params)*> PartialOrd for $ty {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<$($ty_params)*> Ord for $ty {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }

        impl<$($ty_params)*> Hash for $ty {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.0.hash(state);
            }
        }

        impl<$($ty_params)*> fmt::Debug for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let (ptr, tag) = self.get();
                f.debug_struct($name_str)
                    .field("ptr", &ptr)
                    .field("tag", &tag)
                    .finish()
            }
        }
    }; };
}

pub mod implied;

pub struct TaggedPtr<T, const BITS: Bits>(PtrImpl<T, ConstBits<BITS>>);

impl<T, const BITS: Bits> TaggedPtr<T, BITS> {
    /// The number of bits that this tagged pointer can store.
    pub const BITS: u32 = BITS;

    /// The maximum tag (inclusive) that this tagged pointer can store. Equal
    /// to `(1 << BITS) - 1` (i.e., one less than 2 to the power of `BITS`).
    pub const MAX_TAG: usize = PtrImpl::<T, ConstBits<BITS>>::MASK;

    /// Creates a new tagged pointer. Only the lower `BITS` bits of `tag` are
    /// stored.
    ///
    /// `ptr` should be “dereferenceable” in the sense defined by
    /// [`core::ptr`](core::ptr#safety).[^1] Otherwise, the pointers returned
    /// by [`Self::get`] and [`Self::ptr`] may not be equivalent to `ptr`---it
    /// may be unsound to use them in ways that are sound for `ptr`.
    ///
    /// # Panics
    ///
    /// This function may panic if `ptr` is not aligned to at least
    /// 2<sup>`BITS`</sup> (i.e.,
    /// <code>[mem::align_of]::\<T>().[trailing_zeros]()</code> must be greater
    /// than or equal to `BITS`). It is recommended that `ptr` be properly
    /// aligned for `T`, which automatically fulfills this requirement.
    ///
    /// [trailing_zeros]: usize::trailing_zeros
    ///
    /// [^1]: It is permissible for only the first 2<sup>`BITS`</sup> bytes of
    /// `ptr` to be dereferenceable.
    pub fn new(ptr: NonNull<T>, tag: usize) -> Self {
        Self(PtrImpl::new(ptr, tag))
    }

    /// Creates a new tagged pointer.
    ///
    /// Equivalent to [`Self::new`] but without some runtime checks. The
    /// comments about `ptr` being “dereferenceable” also apply to this
    /// function.
    ///
    /// # Safety
    ///
    /// * `ptr` must be aligned to at least 2<sup>`BITS`</sup> (i.e.,
    ///   <code>[mem::align_of]::\<T>().[trailing_zeros]()</code> must be
    ///   greater than or equal to `BITS`).
    /// * `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(ptr: NonNull<T>, tag: usize) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { PtrImpl::new_unchecked(ptr, tag) })
    }
}

impl_tagged_ptr_common!(
    [T, const BITS: Bits],
    TaggedPtr<T, BITS>,
    "TaggedPtr",
    "# impl<T, const B: Bits> Ext for
     tagged_pointer::TaggedPtr<T, B>",
);
