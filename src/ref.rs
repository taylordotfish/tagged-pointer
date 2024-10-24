/*
 * Copyright 2023-2024 Jonáš Fiala <jonas.fiala@inf.ethz.ch>
 * Copyright 2023-2024 taylor.fish <contact@taylor.fish>
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

use core::borrow::{Borrow, BorrowMut};
use core::fmt;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

use super::Bits;
use super::implied::TaggedPtr;

/// A tagged immutable reference: a space-efficient representation of a
/// reference and integer tag.
///
/// This type stores a shared reference and an integer tag without taking up
/// more space than a normal reference (unless the fallback implementation is
/// used; see the [crate documentation](crate#assumptions)).
///
/// The tagged reference conceptually holds a `&'a T` and a certain number of
/// bits of an integer tag.
///
/// The number of bits that can be stored in the tag is determined as
/// `mem::align_of::<T>().trailing_zeros()`, any higher bits in the tag will
/// be masked away. See [`Self::new`] for more details.
#[repr(transparent)]
pub struct TaggedRef<'a, T>(
    TaggedPtr<T>,
    PhantomData<&'a T>,
);

impl<'a, T> TaggedRef<'a, T> {
    /// Creates a new tagged reference. Only the lower `BITS` bits of `tag` are
    /// stored.
    ///
    /// A check is performed at compile time to ensure that the alignment of
    /// `T` is exactly 2<sup>`BITS`</sup> (i.e. that `BITS ==
    /// mem::align_of::<T>().trailing_zeros()`). This ensures
    /// that all properly aligned pointers to `T` will be aligned enough to
    /// store the specified number of bits of the tag.
    pub fn new<const BITS: Bits>(reference: &'a T, tag: usize) -> Self {
        Self::new_implied(reference, tag)
    }

    /// Creates a new tagged reference. Identical to [`Self::new`] but without
    /// needing to explicitly specify the expected number of available bits.
    /// The number of bits is determined as `mem::align_of::<T>().trailing_zeros()`.
    ///
    /// Using this method is generally not recommended since the tag may be
    /// unexpectedly truncated if the alignment of `T` is not what you expect.
    pub fn new_implied(reference: &'a T, tag: usize) -> Self {
        let ptr = NonNull::from(reference);
        let tag = tag & (core::mem::align_of::<T>() - 1);
        // SAFETY: `reference` is guaranteed to be aligned and `tag <= mask()`.
        let ptr = unsafe { TaggedPtr::new_unchecked(ptr, tag) };
        Self(ptr, PhantomData)
    }

    /// Gets the reference and tag stored by the tagged reference.
    pub fn get(self) -> (&'a T, usize) {
        let (ptr, tag) = self.0.get();
        // SAFETY: `ptr` is properly aligned and “dereferenceable”. The
        // underlying data is initialized and immutable since we hold a shared
        // reference to `self` which has a `PhantomData<&'a T>`. We respect
        // Rust lifetimes by returning a copy of the original reference.
        let ptr = unsafe { ptr.as_ref() };
        (ptr, tag)
    }

    /// Gets the reference stored by the tagged reference, without the tag.
    /// Equivalent to [`self.get().0`](Self::get).
    pub fn reference(self) -> &'a T {
        self.get().0
    }

    /// Sets the reference without modifying the tag.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedRef;
    /// # trait Ext<'a, T> { fn set_reference(&mut self, reference: &'a T); }
    /// # impl<'a, T> Ext<'a, T>
    /// #    for TaggedRef<'a, T> {
    /// # fn set_reference(&mut self, reference: &'a T) {
    /// *self = Self::new_implied(reference, self.tag());
    /// # }}
    /// ```
    ///
    /// Note that this method does not kill the original borrow, so the
    /// following will not compile:
    ///
    /// ```compile_fail
    /// # use tagged_pointer::TaggedRef;
    /// let (mut x, y) = (14_u32, 21_u32);
    /// let mut tr = TaggedRef::new::<2>(&x, 0);
    /// tr.set_reference(&y); // `x` stays borrowed
    /// x += 1; // use of borrowed `x`
    /// let v = *tr;
    /// ```
    ///
    /// If you run into this issue, use [`Self::new_reference`] instead.
    pub fn set_reference(&mut self, reference: &'a T) {
        *self = Self::new_implied(reference, self.tag());
    }

    /// Creates a new tagged reference with the same tag.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedRef;
    /// # trait Ext<T> { fn set_reference<'b>
    /// #    (&mut self, reference: &'b T) -> TaggedRef<'b, T>; }
    /// # impl<'a, T> Ext<T>
    /// #    for TaggedRef<'a, T> {
    /// # fn set_reference<'b>(&mut self, reference: &'b T)
    /// #    -> TaggedRef<'b, T> {
    /// TaggedRef::new_implied(reference, self.tag())
    /// # }}
    /// ```
    ///
    /// Unlike [`Self::set_reference`] this allows `self` to be dropped, so the
    /// following compiles:
    ///
    /// ```
    /// # use tagged_pointer::TaggedRef;
    /// let (mut x, y) = (14_u32, 21_u32);
    /// let mut tr = TaggedRef::new::<2>(&x, 0);
    /// // Drops old `tr` so `x` no longer borrowed
    /// tr = tr.new_reference(&y);
    /// x += 1;
    /// let v = *tr;
    /// ```
    pub fn new_reference<'b>(
        self,
        reference: &'b T,
    ) -> TaggedRef<'b, T> {
        TaggedRef::new_implied(reference, self.tag())
    }

    /// Gets the tag stored by the tagged reference. Equivalent to
    /// [`self.get().1`](Self::get).
    pub fn tag(self) -> usize {
        self.get().1
    }

    /// Sets the tag without modifying the reference. Only the lower `BITS`
    /// bits of `tag` are stored.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedRef;
    /// # trait Ext { fn set_tag<const BITS: u32>(&mut self, tag: usize); }
    /// # impl<'a, T> Ext for TaggedRef<'a, T> {
    /// # fn set_tag<const BITS: u32>(&mut self, tag: usize) {
    /// *self = Self::new::<BITS>(self.reference(), tag);
    /// # }}
    /// ```
    pub fn set_tag<const BITS: Bits>(&mut self, tag: usize) {
        *self = Self::new_implied(self.reference(), tag);
    }
}

impl<'a, T> Clone for TaggedRef<'a, T> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}

impl<'a, T> Copy for TaggedRef<'a, T> {}

macro_rules! derive_common {
    ($name:ident) => {
        impl<'a, T> Deref for $name<'a, T> {
            type Target = T;

            fn deref(&self) -> &Self::Target {
                self.reference()
            }
        }

        impl<'a, T> Borrow<T> for $name<'a, T> {
            fn borrow(&self) -> &T {
                self.deref()
            }
        }

        impl<'a, T> fmt::Pointer for $name<'a, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Pointer::fmt(&self.reference(), f)
            }
        }
    };
}

derive_common!(TaggedRef);

/// A tagged mutable reference: a space-efficient representation of a reference
/// and integer tag.
///
/// This type stores an exclusive reference and an integer tag without taking
/// up more space than a normal reference (unless the fallback implementation
/// is used; see the [crate documentation](crate#assumptions)).
///
/// The tagged reference conceptually holds a `&'a mut T` and a certain number
/// of bits of an integer tag.
///
/// The number of bits that can be stored in the tag is determined as
/// `mem::align_of::<T>().trailing_zeros()`, any higher bits in the tag will
/// be masked away. See [`Self::new`] for more details.
#[repr(transparent)]
pub struct TaggedMutRef<'a, T>(
    TaggedPtr<T>,
    PhantomData<&'a mut T>,
);

impl<'a, T> TaggedMutRef<'a, T> {
    /// Creates a new tagged reference. Only the lower `BITS` bits of `tag` are
    /// stored.
    ///
    /// A check is performed at compile time to ensure that the alignment of
    /// `T` is exactly 2<sup>`BITS`</sup> (i.e. that `BITS ==
    /// mem::align_of::<T>().trailing_zeros()`). This ensures
    /// that all properly aligned pointers to `T` will be aligned enough to
    /// store the specified number of bits of the tag.
    pub fn new<const BITS: Bits>(reference: &'a mut T, tag: usize) -> Self {
        Self::new_implied(reference, tag)
    }

    /// Creates a new tagged reference. Identical to [`Self::new`] but without
    /// needing to explicitly specify the expected number of available bits.
    /// The number of bits is determined as `mem::align_of::<T>().trailing_zeros()`.
    ///
    /// Using this method is generally not recommended since the tag may be
    /// unexpectedly truncated if the alignment of `T` is not what you expect.
    pub fn new_implied(reference: &'a mut T, tag: usize) -> Self {
        let ptr = NonNull::from(reference);
        let tag = tag & (core::mem::align_of::<T>() - 1);
        // SAFETY: `reference` is guaranteed to be aligned and `tag <= mask()`.
        let ptr = unsafe { TaggedPtr::new_unchecked(ptr, tag) };
        Self(ptr, PhantomData)
    }

    /// Immutably gets the reference and tag stored by the tagged reference. If you
    /// need both the reference and tag, this method may be more efficient than
    /// calling [`Self::tag`] and [`Self::reference`] separately.
    pub fn get(&self) -> (&T, usize) {
        let (ptr, tag) = self.0.get();
        // SAFETY: `ptr` is properly aligned and “dereferenceable”. The
        // underlying data is initialized and immutable since we hold a shared
        // reference to a unique `self` (`TaggedMutRef` is not duplicable)
        // which has a `PhantomData<&'a mut T>`. We respect Rust lifetimes by
        // returning a reference which will not live longer than the input
        // reference (which cannot outlive `'a`) and thus prevent mutable use
        // of `self` while the returned immutable reference is live.
        let ptr = unsafe { ptr.as_ref() };
        (ptr, tag)
    }

    /// Mutably gets the reference and tag stored by the tagged reference. If you
    /// need both the reference and tag, this method may be more efficient than
    /// calling [`Self::tag`] and [`Self::reference_mut`] separately.
    pub fn get_mut(&mut self) -> (&mut T, usize) {
        // SAFETY: can only have been constructed with `TaggedMutRef::new`.
        // Thus `ptr` will be properly aligned and “dereferenceable”.
        let (mut ptr, tag) = self.0.get();
        // SAFETY: `ptr` is properly aligned and “dereferenceable”. The
        // underlying data is initialized and unaliased since we hold a unique
        // reference to a unique `self` (`TaggedMutRef` is not duplicable)
        // which has a `PhantomData<&'a mut T>`. We respect Rust lifetimes by
        // returning a reference which will not live longer than the input
        // reference (which cannot outlive `'a`) and thus prevent any use of
        // `self` while the returned mutable reference is live.
        let ptr = unsafe { ptr.as_mut() };
        (ptr, tag)
    }

    /// Deconstructs the tagged reference to get back the arguments (reference and
    /// tag) passed to [`Self::new`]. If you need both the reference and tag,
    /// this method may be more efficient than calling [`Self::tag`] and
    /// [`Self::reference_inner`] separately.
    pub fn get_inner(self) -> (&'a mut T, usize) {
        // SAFETY: can only have been constructed with `TaggedMutRef::new`.
        // Thus `ptr` will be properly aligned and “dereferenceable”.
        let (mut ptr, tag) = self.0.get();
        // SAFETY: `ptr` is properly aligned and “dereferenceable”. The
        // underlying data is initialized and unaliased since we hold a unique
        // `self` (`TaggedMutRef` is not duplicable) which has a
        // `PhantomData<&'a mut T>`. We respect Rust lifetimes by moving out
        // the original reference (`self` is dropped).
        let ptr = unsafe { ptr.as_mut() };
        (ptr, tag)
    }

    /// Immutably gets the reference stored by the tagged reference, without
    /// the tag. Equivalent to [`self.get().0`](Self::get).
    pub fn reference(&self) -> &T {
        self.get().0
    }

    /// Mutably gets the reference stored by the tagged reference, without the
    /// tag. Equivalent to [`self.get_mut().0`](Self::get_mut).
    pub fn reference_mut(&mut self) -> &mut T {
        self.get_mut().0
    }

    /// Gets the reference stored by the tagged reference, without the tag. The
    /// tag is lost. Equivalent to [`self.get_inner().0`](Self::get_inner).
    pub fn reference_inner(self) -> &'a mut T {
        self.get_inner().0
    }

    /// Sets the reference without modifying the tag.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// # trait Ext<'a, T>
    /// #    { fn set_reference(&mut self, reference: &'a mut T); }
    /// # impl<'a, T> Ext<'a, T>
    /// #    for TaggedMutRef<'a, T> {
    /// # fn set_reference(&mut self, reference: &'a mut T) {
    /// *self = Self::new_implied(reference, self.tag());
    /// # }}
    /// ```
    ///
    /// Note that this method does not kill the original borrow, so the
    /// following will not compile:
    ///
    /// ```compile_fail
    /// # use tagged_pointer::TaggedMutRef;
    /// let (mut x, mut y) = (14_u32, 21_u32);
    /// let mut tr = TaggedMutRef::new::<2>(&mut x, 0);
    /// tr.set_reference(&mut y); // `x` stays borrowed
    /// x += 1; // use of borrowed `x`
    /// *tr += 1;
    /// ```
    ///
    /// If you run into this issue, use [`Self::new_reference`] instead.
    pub fn set_reference(&mut self, reference: &'a mut T) {
        *self = Self::new_implied(reference, self.tag());
    }

    /// Creates a new tagged reference with the same tag.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// # trait Ext<T> { fn set_reference<'b>
    /// #    (&mut self, reference: &'b mut T) -> TaggedMutRef<'b, T>; }
    /// # impl<'a, T> Ext<T>
    /// #    for TaggedMutRef<'a, T> {
    /// # fn set_reference<'b>(&mut self, reference: &'b mut T)
    /// #    -> TaggedMutRef<'b, T> {
    /// TaggedMutRef::new_implied(reference, self.tag())
    /// # }}
    /// ```
    ///
    /// Unlike [`Self::set_reference`] this allows `self` to be dropped, so the
    /// following compiles:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// let (mut x, mut y) = (14_u32, 21_u32);
    /// let mut tr = TaggedMutRef::new::<2>(&mut x, 0);
    /// // Drops old `tr` so `x` no longer borrowed
    /// tr = tr.new_reference(&mut y);
    /// x += 1;
    /// *tr += 1;
    /// ```
    pub fn new_reference<'b>(
        &self,
        reference: &'b mut T,
    ) -> TaggedMutRef<'b, T> {
        TaggedMutRef::new_implied(reference, self.tag())
    }

    /// Gets the tag stored by the tagged reference. Equivalent to
    /// [`self.get().1`](Self::get).
    pub fn tag(&self) -> usize {
        self.get().1
    }

    /// Sets the tag without modifying the reference. Only the lower `BITS`
    /// bits of `tag` are stored.
    ///
    /// This method only requires a mutable reference to `self`, while being
    /// equivalent to the owned version:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// let mut x = 14_u32;
    /// let mut tr = TaggedMutRef::new::<2>(&mut x, 0);
    /// // The following two are equivalent:
    /// tr.set_tag::<2>(1);
    /// tr = TaggedMutRef::new::<2>(tr.reference_inner(), 1);
    /// ```
    pub fn set_tag<const BITS: Bits>(&mut self, tag: usize) {
        let mut ptr = NonNull::from(self.reference_mut());
        // SAFETY: We can extend the lifetime to `'a` since we know that this
        // is the true lifetime of the reference `self` holds. We temporarily
        // mutably alias through `self` and `reference` but we're about to
        // overwrite `self` so it's ok. Beware that if `Self::new` could panic
        // then `self` would not get overwritten, luckily this would still be
        // ok because `reference` is immediately discarded on return.
        let reference = unsafe { ptr.as_mut() };
        *self = Self::new_implied(reference, tag);
    }

    /// Creates a new identical tagged reference. Useful to mimic the reborrow
    /// which Rust automatically does for mutable references in various places.
    ///
    /// This method is simply equivalent to:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// # trait Ext<T> { fn reborrow<'b>(&'b mut self)
    /// #    -> TaggedMutRef<'b, T>; }
    /// # impl<'a, T> Ext<T>
    /// #    for TaggedMutRef<'a, T> {
    /// # fn reborrow<'b>(&'b mut self) -> TaggedMutRef<'b, T> {
    /// let (reference, tag) = self.get_mut();
    /// TaggedMutRef::new_implied(reference, tag)
    /// # }}
    /// ```
    ///
    /// Use this for example when calling a function:
    ///
    /// ```
    /// # use tagged_pointer::TaggedMutRef;
    /// fn foo<T>(tr: TaggedMutRef<T>) {
    ///     // ...
    /// }
    /// let mut x = 14_u32;
    /// let mut tr = TaggedMutRef::new::<2>(&mut x, 0);
    /// foo(tr.reborrow());
    /// *tr += 1; // cannot use `tr` without the `reborrow` above
    /// ```
    pub fn reborrow<'b>(&'b mut self) -> TaggedMutRef<'b, T> {
        let (reference, tag) = self.get_mut();
        TaggedMutRef::new_implied(reference, tag)
    }
}

impl<'a, T> DerefMut for TaggedMutRef<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.reference_mut()
    }
}

impl<'a, T> BorrowMut<T> for TaggedMutRef<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self.deref_mut()
    }
}

derive_common!(TaggedMutRef);
