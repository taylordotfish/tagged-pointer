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

use core::marker::PhantomData;
use core::ptr;
use crate::implied::TaggedPtr;

macro_rules! impl_implied_tagged_ref_common {
    ($name:ident) => {
        impl<T> $name<'_, T> {
            /// The number of tag bits that this tagged reference can store.
            pub const BITS: u32 = TaggedPtr::<T>::BITS;

            /// The maximum tag (inclusive) that this tagged reference can
            /// store. Equal to <code>[mem::align_of]::\<T>() - 1</code>.
            pub const MAX_TAG: usize = TaggedPtr::<T>::MAX_TAG;
        }
    };
}

macro_rules! impl_tagged_ref_shared_mut_common {
    (
        $name:ident,
        [$($ty_params:tt)*],
        [$($ty_args:tt)*],
        is_wrapper: cfg($wrapper:meta) $(,)?
    ) => { const _: () = {
        use core::cmp::Ordering;
        use core::fmt::{self, Debug};
        use core::hash::{Hash, Hasher};
        #[cfg(doc)]
        use core::mem;

        impl<$($ty_params)*> Eq for $name<'_, $($ty_args)*>
        where
            T: Eq,
        {
        }

        impl<$($ty_params)*> PartialEq for $name<'_, $($ty_args)*>
        where
            T: PartialEq,
        {
            /// Returns <code>self.[get]() == other.[get]()</code>.
            ///
            /// [get]: Self::get
            fn eq(&self, other: &Self) -> bool {
                #[cfg(not($wrapper))]
                {
                    self.get() == other.get()
                }
                #[cfg($wrapper)]
                {
                    self.0 == other.0
                }
            }
        }

        impl<$($ty_params)*> Ord for $name<'_, $($ty_args)*>
        where
            T: Ord,
        {
            /// Returns <code>self.[get]().cmp(&other.[get]())</code>.
            ///
            /// [get]: Self::get
            fn cmp(&self, other: &Self) -> Ordering {
                #[cfg(not($wrapper))]
                {
                    self.get().cmp(&other.get())
                }
                #[cfg($wrapper)]
                {
                    self.0.cmp(&other.0)
                }
            }
        }

        impl<$($ty_params)*> PartialOrd for $name<'_, $($ty_args)*>
        where
            T: PartialOrd,
        {
            /// Returns <code>self.[get]().partial_cmp(&other.[get]())</code>.
            ///
            /// [get]: Self::get
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                #[cfg(not($wrapper))]
                {
                    self.get().partial_cmp(&other.get())
                }
                #[cfg($wrapper)]
                {
                    self.0.partial_cmp(&other.0)
                }
            }
        }

        impl<$($ty_params)*> Hash for $name<'_, $($ty_args)*>
        where
            T: Hash,
        {
            /// Hashes [`self.get()`](Self::get).
            fn hash<H: Hasher>(&self, state: &mut H) {
                #[cfg(not($wrapper))]
                {
                    self.get().hash(state)
                }
                #[cfg($wrapper)]
                {
                    self.0.hash(state)
                }
            }
        }

        // Note: we can't implement `Borrow<T>` because `Eq`, `Ord`, and `Hash`
        // on tagged references don't behave the same as their implementations
        // for `&T`.
        //
        // `Deref<Target = T>` isn't implemented because this type is intended
        // to be conceptually equivalent to a struct with individual
        // `reference: &T` and `tag: usize` fields, which would typically
        // require explicit accessing of the `reference` field. This also
        // avoids conflicts with the inherent `TaggedRef` methods and makes it
        // easier to add new methods in the future without worrying about
        // compatibility.
        impl<$($ty_params)*> AsRef<T> for $name<'_, $($ty_args)*> {
            fn as_ref(&self) -> &T {
                #[cfg(not($wrapper))]
                {
                    self.get_ref()
                }
                #[cfg($wrapper)]
                {
                    self.0.as_ref()
                }
            }
        }

        impl<$($ty_params)*> Debug for $name<'_, $($ty_args)*>
        where
            T: Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                #[cfg(not($wrapper))]
                {
                    let (r, tag) = self.get();
                    f.debug_struct(stringify!($name))
                        .field("data", r)
                        .field("tag", &tag)
                        .finish()
                }
                #[cfg($wrapper)]
                {
                    write!(f, "{:?}", self.0)
                }
            }
        }

        impl<$($ty_params)*> fmt::Pointer for $name<'_, $($ty_args)*> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                #[cfg(not($wrapper))]
                {
                    write!(f, "{:p}", self.get_ref())
                }
                #[cfg($wrapper)]
                {
                    write!(f, "{:p}", self.0)
                }
            }
        }
    }; };
}

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
pub struct TaggedRef<'a, T>(TaggedPtr<T>, PhantomData<&'a T>);

impl<'a, T> TaggedRef<'a, T> {
    /// Creates a new tagged reference. Only the lower [`Self::BITS`] bits of
    /// `tag` are stored.
    pub fn new(reference: &'a T, tag: usize) -> Self {
        let tag = tag & Self::MAX_TAG;
        // SAFETY: `tag` cannot be greater than `MAX_TAG` after the
        // bitwise-and.
        unsafe { Self::new_unchecked(reference, tag) }
    }

    /// Equivalent to [`Self::new`] but without some runtime checks.
    ///
    /// # Safety
    ///
    /// `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(reference: &'a T, tag: usize) -> Self {
        let ptr = reference.into();
        // SAFETY: References are necessarily aligned and
        // dereferenceable. The validity of `tag` is ensured by the
        // caller.
        let tp = unsafe { TaggedPtr::new_unchecked(ptr, tag) };
        Self(tp, PhantomData)
    }
}

macro_rules! impl_tagged_ref_methods {
    (
        [$($ty_args:tt)*],
        is_wrapper: cfg($wrapper:meta),
        $doctest_context:literal $(,)?
    ) => {
        /// Gets the reference and tag stored by the tagged reference.
        pub fn get(self) -> (&'a T, usize) {
            #[cfg(not($wrapper))]
            {
                let (ptr, tag) = self.0.get();
                // SAFETY: `ptr` came from the valid reference passed to
                // `Self::new`. The `PhantomData` in `self.1` has the
                // appropriate lifetime to ensure the reference is still valid.
                (unsafe { ptr.as_ref() }, tag)
            }
            #[cfg($wrapper)]
            {
                self.0.get()
            }
        }

        /// Gets the reference stored by the tagged reference, without the tag.
        ///
        /// Equivalent to [`self.get().0`](Self::get).
        pub fn get_ref(self) -> &'a T {
            #[cfg(not($wrapper))]
            {
                self.get().0
            }
            #[cfg($wrapper)]
            {
                self.0.get_ref()
            }
        }

        /// Sets the reference without modifying the tag.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// #[doc = $doctest_common]
        /// # trait Ext<'a, T> { fn f(&mut self, reference: &'a T); }
        /// # impl<'a, T> Ext<'a, T> for TaggedRef<'a, T> {
        /// # fn f(&mut self, reference: &'a T) {
        /// *self = self.with_ref(reference);
        /// # }}
        /// ```
        ///
        /// Because this method mutates the tagged reference in-place, the new
        /// reference must have the exact same lifetime, `'a`. As a
        /// consequence, any data currently borrowed for `'a` by the old
        /// reference will remain borrowed even once the reference is updated.
        ///
        /// [`Self::with_ref`] may be more flexible in some situations, as it
        /// returns a new tagged reference that can have a different lifetime.
        pub fn set_ref(&mut self, reference: &'a T) {
            #[cfg(not($wrapper))]
            {
                *self = self.with_ref(reference);
            }
            #[cfg($wrapper)]
            {
                self.0.set_ref(reference)
            }
        }

        /// Creates a new tagged reference with the same tag but a different
        /// reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// #[doc = $doctest_common]
        /// # trait Ext<'a, T> {
        /// #     fn f<'b>(&mut self, reference: &'b T) -> TaggedRef<'b, T>;
        /// # }
        /// # impl<'a, T> Ext<'a, T> for TaggedRef<'a, T> {
        /// # fn f<'b>(&mut self, reference: &'b T) -> TaggedRef<'b, T> {
        /// TaggedRef::new(reference, self.tag())
        /// # }}
        /// ```
        pub fn with_ref<'b>(
            self,
            reference: &'b T,
        ) -> TaggedRef<'b, $($ty_args)*> {
            #[cfg(not($wrapper))]
            {
                TaggedRef::new(reference, self.tag())
            }
            #[cfg($wrapper)]
            {
                TaggedRef(self.0.with_ref(reference))
            }
        }

        /// Gets the tag stored by the tagged reference. Equivalent to
        /// [`self.get().1`](Self::get).
        pub fn tag(self) -> usize {
            #[cfg(not($wrapper))]
            {
                self.get().1
            }
            #[cfg($wrapper)]
            {
                self.0.tag()
            }
        }

        /// Sets the tag without modifying the reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// #[doc = $doctest_common]
        /// # trait Ext<'a, T> { fn f(&mut self, tag: usize); }
        /// # impl<'a, T> Ext<'a, T> for TaggedRef<'a, T> {
        /// # fn f(&mut self, tag: usize) {
        /// *self = Self::new(self.get_ref(), tag);
        /// # }}
        /// ```
        pub fn set_tag(&mut self, tag: usize) {
            #[cfg(not($wrapper))]
            {
                *self = Self::new(self.get_ref(), tag);
            }
            #[cfg($wrapper)]
            {
                self.0.set_tag(tag)
            }
        }
    };
}

macro_rules! impl_tagged_ref_common {
    (
        [$($ty_params:tt)*],
        [$($ty_args:tt)*],
        is_wrapper: cfg($wrapper:meta),
        $doctest_context:literal $(,)?
    ) => {
        impl_tagged_ref_shared_mut_common!(
            TaggedRef,
            [$($ty_params)*],
            [$($ty_args)*],
            is_wrapper: cfg($wrapper),
        );

        impl<'a, $($ty_params)*> TaggedRef<'a, $($ty_args)*> {
            impl_tagged_ref_methods!(
                [$($ty_args)*],
                is_wrapper: cfg($wrapper),
                $doctest_context,
            );
        }

        impl<$($ty_params)*> Clone for TaggedRef<'_, $($ty_args)*> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<$($ty_params)*> Copy for TaggedRef<'_, $($ty_args)*> {}
    };
}

impl_implied_tagged_ref_common!(TaggedRef);
impl_tagged_ref_common!(
    [T],
    [T],
    is_wrapper: cfg(any()),
    "# use tagged_pointer::implied::TaggedRef;",
);

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
pub struct TaggedMutRef<'a, T>(TaggedPtr<T>, PhantomData<&'a mut T>);

impl<'a, T> TaggedMutRef<'a, T> {
    /// Creates a new tagged mutable reference. Only the lower [`Self::BITS`]
    /// bits of `tag` are stored.
    pub fn new(reference: &'a mut T, tag: usize) -> Self {
        let tag = tag & Self::MAX_TAG;
        // SAFETY: `tag` cannot be greater than `MAX_TAG` after the
        // bitwise-and.
        unsafe { Self::new_unchecked(reference, tag) }
    }

    /// Equivalent to [`Self::new`] but without some runtime checks.
    ///
    /// # Safety
    ///
    /// `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(reference: &'a mut T, tag: usize) -> Self {
        let ptr = reference.into();
        // SAFETY: References are necessarily aligned and dereferenceable. The
        // validity of `tag` is ensured by the caller.
        Self(unsafe { TaggedPtr::new_unchecked(ptr, tag) }, PhantomData)
    }
}

macro_rules! impl_tagged_mut_ref_methods {
    (
        [$($ty_args:tt)*],
        is_wrapper: cfg($wrapper:meta),
        $doctest_context:literal $(,)?
    ) => {
        /// Creates an immutable [`TaggedRef`] with the same reference and tag.
        ///
        /// This method reborrows the reference; see also
        /// [`Self::into_tagged_ref`], which preserves the lifetime.
        pub fn to_tagged_ref(&self) -> TaggedRef<'_, $($ty_args)*> {
            #[cfg(not($wrapper))]
            {
                // The return type of this method ensures that Rust's standard
                // borrowing rules will guarantee soundness. The `TaggedRef`
                // can't outlive `'a` (its lifetime is that of `self`) , and
                // the data can't be mutated while the `TaggedRef` is active,
                // since this method borrows the `TaggedMutRef` immutably.
                TaggedRef(self.0, PhantomData)
            }
            #[cfg($wrapper)]
            {
                TaggedRef(self.0.to_tagged_ref())
            }
        }

        /// Converts the tagged reference into an immutable [`TaggedRef`].
        ///
        /// [`Self::to_tagged_ref`] reborrows the reference instead of
        /// consuming the [`TaggedMutRef`].
        pub fn into_tagged_ref(self) -> TaggedRef<'a, $($ty_args)*> {
            #[cfg(not($wrapper))]
            {
                // The `TaggedMutRef` is consumed, preventing future mutable
                // access, so it's safe to return a `TaggedRef` with the same
                // lifetime.
                TaggedRef(self.0, PhantomData)
            }
            #[cfg($wrapper)]
            {
                TaggedRef(self.0.into_tagged_ref())
            }
        }

        /// Returns an immutable reborrow of the reference stored by the tagged
        /// reference, along with a copy of the tag.
        ///
        /// See [`Self::get_mut`] if you need a mutable reference.
        pub fn get(&self) -> (&T, usize) {
            #[cfg(not($wrapper))]
            {
                self.to_tagged_ref().get()
            }
            #[cfg($wrapper)]
            {
                self.0.get()
            }
        }

        /// Returns a mutable reborrow of the reference stored by the tagged
        /// reference, along with a copy of the tag.
        pub fn get_mut(&mut self) -> (&mut T, usize) {
            #[cfg(not($wrapper))]
            {
                let (mut ptr, tag) = self.0.get();
                // SAFETY: `ptr` came from the valid reference passed to
                // `Self::new`. The `PhantomData` in `self.1` has the
                // appropriate lifetime to ensure the reference is still valid,
                // and the return type of this method has the correct lifetime
                // to ensure the data cannot be aliased.
                (unsafe { ptr.as_mut() }, tag)
            }
            #[cfg($wrapper)]
            {
                self.0.get_mut()
            }
        }

        /// Deconstructs the tagged reference into its constituent parts: the
        /// reference (with the original lifetime `'a`) and the tag.
        pub fn into_inner(self) -> (&'a mut T, usize) {
            #[cfg(not($wrapper))]
            {
                let (mut ptr, tag) = self.0.get();
                // SAFETY: `ptr` came from the valid reference passed to
                // `Self::new`. The `PhantomData` in `self.1` has the
                // appropriate lifetime to ensure the reference is still valid,
                // and this method takes ownership of `self` to ensure the data
                // cannot be aliased.
                (unsafe { ptr.as_mut() }, tag)
            }
            #[cfg($wrapper)]
            {
                self.0.into_inner()
            }
        }

        /// Returns an immutable reborrow of the reference stored by the tagged
        /// reference.
        ///
        /// See [`Self::get_mut_ref`] if you need a mutable reference.
        pub fn get_ref(&self) -> &T {
            #[cfg(not($wrapper))]
            {
                self.get().0
            }
            #[cfg($wrapper)]
            {
                self.0.get_ref()
            }
        }

        /// Returns a mutable reborrow of the reference stored by the tagged
        /// reference.
        pub fn get_mut_ref(&mut self) -> &mut T {
            #[cfg(not($wrapper))]
            {
                self.get_mut().0
            }
            #[cfg($wrapper)]
            {
                self.0.get_mut_ref()
            }
        }

        /// Gets the reference stored by the tagged reference with its original
        /// lifetime (`'a`), consuming the tagged reference in the process.
        ///
        /// Equivalent to <code>[Self::into_inner]().0</code>.
        pub fn into_ref(self) -> &'a mut T {
            #[cfg(not($wrapper))]
            {
                self.into_inner().0
            }
            #[cfg($wrapper)]
            {
                self.0.into_ref()
            }
        }

        /// Sets the reference without modifying the tag.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// # trait Ext<'a, T> { fn f(&mut self, reference: &'a mut T); }
        /// # impl<'a, T> Ext<'a, T> for TaggedMutRef<'a, T> {
        /// # fn f(&mut self, reference: &'a mut T) {
        /// *self = self.with_ref(reference);
        /// # }}
        /// ```
        ///
        /// Because this method mutates the tagged reference in-place, the new
        /// reference must have the exact same lifetime, `'a`. As a
        /// consequence, any data currently borrowed for `'a` by the old
        /// reference will remain borrowed even once the reference is updated.
        ///
        /// [`Self::with_ref`] may be more flexible in some situations, as it
        /// returns a new tagged reference that can have a different lifetime.
        pub fn set_ref(&mut self, reference: &'a mut T) {
            #[cfg(not($wrapper))]
            {
                *self = self.with_ref(reference);
            }
            #[cfg($wrapper)]
            {
                self.0.set_ref(reference)
            }
        }

        /// Creates a new tagged reference with the same tag but a different
        /// reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// # trait Ext<T> {
        /// #     fn f<'b>(&mut self, r: &'b mut T) -> TaggedMutRef<'b, T>;
        /// # }
        /// # impl<T> Ext<T> for TaggedMutRef<'_, T> {
        /// # fn f<'b>(
        /// #     &mut self, reference: &'b mut T,
        /// # ) -> TaggedMutRef<'b, T> {
        /// TaggedMutRef::new(reference, self.tag())
        /// # }}
        /// ```
        pub fn with_ref<'b>(
            &self,
            reference: &'b mut T,
        ) -> TaggedMutRef<'b, $($ty_args)*> {
            #[cfg(not($wrapper))]
            {
                TaggedMutRef::new(reference, self.tag())
            }
            #[cfg($wrapper)]
            {
                TaggedMutRef(self.0.with_ref(reference))
            }
        }

        /// Gets the tag stored by the tagged reference. Equivalent to
        /// [`self.get().1`](Self::get).
        pub fn tag(&self) -> usize {
            #[cfg(not($wrapper))]
            {
                self.get().1
            }
            #[cfg($wrapper)]
            {
                self.0.tag()
            }
        }

        /// Sets the tag without modifying the reference.
        ///
        /// This method behaves like the following, but it doesn't require
        /// ownership of the tagged reference:
        ///
        /// ```compile_fail
        /// # trait Ext<T> { fn f(&mut self, tag: usize); }
        /// # impl<T> Ext<T> for TaggedMutRef<'_, T> {
        /// # fn f(&mut self, tag: usize) {
        /// // Error: can't call `into_ref` on `&mut Self`.
        /// *self = Self::new(self.into_ref(), tag);
        /// # }}
        /// ```
        pub fn set_tag(&mut self, tag: usize) {
            #[cfg(not($wrapper))]
            {
                // SAFETY: `self` is a valid reference, so it's safe to read
                // from it, but because `Self` is not `Copy`, we must ensure it
                // isn't accessed until another value is written to it with
                // `ptr::write`. (Conceptually, we're temporarily taking
                // ownership of `*self`.)
                let this = unsafe { ptr::read(self) };
                let this = Self::new(this.into_ref(), tag);
                // SAFETY: `self` is a mutable reference, so it is necessarily
                // aligned and valid for writes.
                unsafe {
                    ptr::write(self, this);
                }
            }
            #[cfg($wrapper)]
            {
                self.0.set_tag(tag)
            }
        }

        /// Creates a new tagged reference that reborrows the referenced data
        /// with a different lifetime.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        /// # trait Ext<T> { fn f(&mut self) -> TaggedMutRef<'_, T>; }
        /// # impl<T> Ext<T> for TaggedMutRef<'_, T> {
        /// # fn f(&mut self) -> TaggedMutRef<'_, T> {
        /// let (reference, tag) = self.get_mut();
        /// TaggedMutRef::new(reference, tag);
        /// # }}
        /// ```
        pub fn reborrow(&mut self) -> TaggedMutRef<'_, $($ty_args)*> {
            #[cfg(not($wrapper))]
            {
                let (reference, tag) = self.get_mut();
                TaggedMutRef::new(reference, tag)
            }
            #[cfg($wrapper)]
            {
                TaggedMutRef(self.0.reborrow())
            }
        }
    };
}

macro_rules! impl_tagged_mut_ref_common {
    (
        [$($ty_params:tt)*],
        [$($ty_args:tt)*],
        is_wrapper: cfg($wrapper:meta),
        $doctest_context:literal $(,)?
    ) => {
        impl_tagged_ref_shared_mut_common!(
            TaggedMutRef,
            [$($ty_params)*],
            [$($ty_args)*],
            is_wrapper: cfg($wrapper),
        );

        impl<'a, $($ty_params)*> TaggedMutRef<'a, $($ty_args)*> {
            impl_tagged_mut_ref_methods!(
                [$($ty_args)*],
                is_wrapper: cfg($wrapper),
                $doctest_context,
            );
        }

        impl<$($ty_params)*> AsMut<T> for TaggedMutRef<'_, $($ty_args)*> {
            fn as_mut(&mut self) -> &mut T {
                #[cfg(not($wrapper))]
                {
                    self.get_mut_ref()
                }
                #[cfg($wrapper)]
                {
                    self.0.as_mut()
                }
            }
        }
    };
}

impl_implied_tagged_ref_common!(TaggedMutRef);
impl_tagged_mut_ref_common!(
    [T],
    [T],
    is_wrapper: cfg(any()),
    "# use tagged_pointer::implied::TaggedMutRef;",
);
