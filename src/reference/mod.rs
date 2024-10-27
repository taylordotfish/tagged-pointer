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

use crate::{Bits, TaggedPtr};
use core::marker::PhantomData;

/// Common code for [`self::TaggedRef`] and [`self::TaggedMutRef`].
macro_rules! impl_explicit_tagged_ref_common {
    ($name:ident $(,)?) => {
        impl<T, const BITS: Bits> $name<'_, T, BITS> {
            /// The number of tag bits that this tagged reference can store.
            pub const BITS: u32 = BITS as _;

            /// The maximum tag (inclusive) that this tagged reference can
            /// store. Equal to `(1 << BITS) - 1` (i.e., one less than 2 to the
            /// power of `BITS`).
            pub const MAX_TAG: usize = Self::max_tag();

            // Separate function show Rustdoc doesn't show the expression
            const fn max_tag() -> usize {
                TaggedPtr::<T, BITS>::MAX_TAG
            }
        }
    };
}

/// Common code for [`TaggedRef`] and [`TaggedMutRef`], as well as the versions
/// in [`implicit`].
macro_rules! impl_tagged_ref_shared_mut_common {
    (
        $name:ident,
        [$($ty_params:tt)*],
        [$($ty_args:tt)*] $(,)?
    ) => { const _: () = {
        use core::cmp::Ordering;
        use core::fmt::{self, Debug};
        use core::hash::{Hash, Hasher};

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
                self.get() == other.get()
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
                self.get().cmp(&other.get())
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
                self.get().partial_cmp(&other.get())
            }
        }

        impl<$($ty_params)*> Hash for $name<'_, $($ty_args)*>
        where
            T: Hash,
        {
            /// Hashes [`self.get()`](Self::get).
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.get().hash(state)
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
                self.get_ref()
            }
        }

        impl<$($ty_params)*> Debug for $name<'_, $($ty_args)*>
        where
            T: Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let (r, tag) = self.get();
                f.debug_struct(stringify!($name))
                    .field("data", r)
                    .field("tag", &tag)
                    .finish()
            }
        }

        impl<$($ty_params)*> fmt::Pointer for $name<'_, $($ty_args)*> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{:p}", self.get_ref())
            }
        }
    }; };
}

with_bits_doc! {
    /// A tagged reference: a space-efficient representation of a reference and
    /// integer tag.
    ///
    /// This type behaves like [`TaggedPtr`] but with a [reference] instead of
    /// a raw pointer.
    #[repr(transparent)]
    pub struct TaggedRef<'a, T, const BITS: Bits>(
        TaggedPtr<T, BITS>,
        PhantomData<&'a T>,
    );
}

impl<'a, T, const BITS: Bits> TaggedRef<'a, T, BITS> {
    /// Creates a new tagged reference. Only the lower `BITS` bits of `tag` are
    /// stored.
    pub fn new(reference: &'a T, tag: usize) -> Self {
        Self::new_impl(reference, tag)
    }
}

/// Common code for [`TaggedRef`] and [`implied::TaggedRef`].
macro_rules! impl_tagged_ref_common {
    (
        [$($ty_params:tt)*],
        [$($ty_args:tt)*],
        $doctest_context:literal $(,)?
    ) => {
        const _: () = {
            use core::marker::PhantomData;

            impl<'a, $($ty_params)*> TaggedRef<'a, $($ty_args)*> {
                impl_tagged_ref_common!(
                    impl methods,
                    [$($ty_args)*],
                    $doctest_context,
                );
            }
        };

        impl<$($ty_params)*> Clone for TaggedRef<'_, $($ty_args)*> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<$($ty_params)*> Copy for TaggedRef<'_, $($ty_args)*> {}

        // SAFETY: `TaggedRef` conceptually holds a `&T` and behaves as such
        // with respect to aliasing and lifetimes. Accordingly, because
        // `T: Sync` implies `&T: Sync`, it is safe for `TaggedRef` to
        // implement `Sync` when the same condition of `T: Sync` holds.
        unsafe impl<$($ty_params)*> Sync for TaggedRef<'_, $($ty_args)*>
        where
            T: Sync,
        {
        }

        // SAFETY: `TaggedRef` conceptually holds a `&T` and behaves as such
        // with respect to aliasing and lifetimes. Accordingly, because
        // `T: Sync` implies `&T: Send`, it is safe for `TaggedRef` to
        // implement `Send` when the same condition of `T: Sync` holds.
        unsafe impl<$($ty_params)*> Send for TaggedRef<'_, $($ty_args)*>
        where
            T: Sync,
        {
        }

        impl_tagged_ref_shared_mut_common!(
            TaggedRef,
            [$($ty_params)*],
            [$($ty_args)*],
        );
    };

    (impl methods, [$($ty_args:tt)*], $doctest_context:literal $(,)?) => {
        // `Self::new` is defined separately for each `TaggedRef` type in order
        // to customize the docstring. This function contains the shared
        // implementation of the function body and is called by `Self::new`.
        fn new_impl(reference: &'a T, tag: usize) -> Self {
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
            // SAFETY: References are necessarily aligned and dereferenceable.
            // The validity of `tag` is ensured by the caller.
            let tp = unsafe { TaggedPtr::new_unchecked(ptr, tag) };
            Self(tp, PhantomData)
        }

        /// Gets the reference and tag stored by the tagged reference.
        pub fn get(self) -> (&'a T, usize) {
            let (ptr, tag) = self.0.get();
            // SAFETY: `ptr` came from the valid reference passed to
            // `Self::new`. The `PhantomData` in `self.1` has the appropriate
            // lifetime to ensure the reference is still valid.
            (unsafe { ptr.as_ref() }, tag)
        }

        /// Gets the reference stored by the tagged reference, without the tag.
        ///
        /// Equivalent to [`self.get().0`](Self::get).
        pub fn get_ref(self) -> &'a T {
            self.get().0
        }

        /// Sets the reference without modifying the tag.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
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
            *self = self.with_ref(reference);
        }

        /// Creates a new tagged reference with the same tag but a different
        /// reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
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
            TaggedRef::new(reference, self.tag())
        }

        /// Gets the tag stored by the tagged reference. Equivalent to
        /// [`self.get().1`](Self::get).
        pub fn tag(self) -> usize {
            self.get().1
        }

        /// Sets the tag without modifying the reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
        /// # trait Ext<'a, T> { fn f(&mut self, tag: usize); }
        /// # impl<'a, T> Ext<'a, T> for TaggedRef<'a, T> {
        /// # fn f(&mut self, tag: usize) {
        /// *self = Self::new(self.get_ref(), tag);
        /// # }}
        /// ```
        pub fn set_tag(&mut self, tag: usize) {
            *self = Self::new(self.get_ref(), tag);
        }
    };
}

impl_explicit_tagged_ref_common!(TaggedRef);
impl_tagged_ref_common!(
    [T, const BITS: Bits],
    [T, BITS],
    "# type TaggedRef<'a, T> = tagged_pointer::TaggedRef<'a, T, 0>;",
);

with_bits_doc! {
    /// Mutable version of [`TaggedRef`].
    ///
    /// Like [`TaggedRef`], this type stores a reference and an integer tag,
    /// but the reference in this type is mutable.
    #[repr(transparent)]
    pub struct TaggedMutRef<'a, T, const BITS: Bits>(
        TaggedPtr<T, BITS>,
        PhantomData<&'a mut T>,
    );
}

impl<'a, T, const BITS: Bits> TaggedMutRef<'a, T, BITS> {
    /// Creates a new tagged mutable reference. Only the lower `BITS` bits of
    /// `tag` are stored.
    pub fn new(reference: &'a mut T, tag: usize) -> Self {
        Self::new_impl(reference, tag)
    }
}

/// Common code for [`TaggedMutRef`] and [`implicit::TaggedMutRef`].
macro_rules! impl_tagged_mut_ref_common {
    (
        [$($ty_params:tt)*],
        [$($ty_args:tt)*],
        $doctest_context:literal $(,)?
    ) => {
        const _: () = {
            use core::marker::PhantomData;
            use core::ptr;

            impl<'a, $($ty_params)*> TaggedMutRef<'a, $($ty_args)*> {
                impl_tagged_mut_ref_common!(
                    impl methods,
                    [$($ty_args)*],
                    $doctest_context,
                );
            }
        };

        impl<$($ty_params)*> AsMut<T> for TaggedMutRef<'_, $($ty_args)*> {
            fn as_mut(&mut self) -> &mut T {
                self.get_mut_ref()
            }
        }

        // SAFETY: `TaggedMutRef` conceptually holds a `&mut T` and behaves as
        // such with respect to aliasing and lifetimes. Accordingly, because
        // `T: Sync` implies `&mut T: Sync`, it is safe for `TaggedMutRef` to
        // implement `Sync` when the same condition of `T: Sync` holds.
        unsafe impl<$($ty_params)*> Sync for TaggedMutRef<'_, $($ty_args)*>
        where
            T: Sync,
        {
        }

        // SAFETY: `TaggedMutRef` conceptually holds a `&mut T` and behaves as
        // such with respect to aliasing and lifetimes. Accordingly, because
        // `T: Send` implies `&mut T: Send`, it is safe for `TaggedRef` to
        // implement `Send` when the same condition of `T: Send` holds.
        unsafe impl<$($ty_params)*> Send for TaggedMutRef<'_, $($ty_args)*>
        where
            T: Send,
        {
        }

        impl_tagged_ref_shared_mut_common!(
            TaggedMutRef,
            [$($ty_params)*],
            [$($ty_args)*],
        );
    };

    (impl methods, [$($ty_args:tt)*], $doctest_context:literal $(,)?) => {
        // `Self::new` is defined separately for each `TaggedMutRef` type in
        // order to customize the docstring. This function contains the shared
        // implementation of the function body and is called by `Self::new`.
        fn new_impl(reference: &'a mut T, tag: usize) -> Self {
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
            // SAFETY: References are necessarily aligned and dereferenceable.
            // The validity of `tag` is ensured by the caller.
            let tp = unsafe { TaggedPtr::new_unchecked(ptr, tag) };
            Self(tp, PhantomData)
        }

        /// Creates an immutable [`TaggedRef`] with the same reference and tag.
        ///
        /// This method reborrows the reference; see also
        /// [`Self::into_tagged_ref`], which preserves the lifetime.
        pub fn to_tagged_ref(&self) -> TaggedRef<'_, $($ty_args)*> {
            // The return type of this method ensures that Rust's standard
            // borrowing rules will guarantee soundness. The `TaggedRef` can't
            // outlive `'a` (its lifetime is that of `self`) , and the data
            // can't be mutated while the `TaggedRef` is active, since this
            // method borrows the `TaggedMutRef` immutably.
            TaggedRef(self.0, PhantomData)
        }

        /// Converts the tagged reference into an immutable [`TaggedRef`].
        ///
        /// [`Self::to_tagged_ref`] reborrows the reference instead of
        /// consuming the [`TaggedMutRef`].
        pub fn into_tagged_ref(self) -> TaggedRef<'a, $($ty_args)*> {
            // The `TaggedMutRef` is consumed, preventing future mutable
            // access, so it's safe to return a `TaggedRef` with the same
            // lifetime.
            TaggedRef(self.0, PhantomData)
        }

        /// Returns an immutable reborrow of the reference stored by the tagged
        /// reference, along with a copy of the tag.
        ///
        /// See [`Self::get_mut`] if you need a mutable reference.
        pub fn get(&self) -> (&T, usize) {
            self.to_tagged_ref().get()
        }

        /// Returns a mutable reborrow of the reference stored by the tagged
        /// reference, along with a copy of the tag.
        pub fn get_mut(&mut self) -> (&mut T, usize) {
            let (mut ptr, tag) = self.0.get();
            // SAFETY: `ptr` came from the valid reference passed to
            // `Self::new`. The `PhantomData` in `self.1` has the appropriate
            // lifetime to ensure the reference is still valid, and the return
            // type of this method has the correct lifetime to ensure the data
            // cannot be aliased.
            (unsafe { ptr.as_mut() }, tag)
        }

        /// Deconstructs the tagged reference into its constituent parts: the
        /// reference (with the original lifetime `'a`) and the tag.
        pub fn into_inner(self) -> (&'a mut T, usize) {
            let (mut ptr, tag) = self.0.get();
            // SAFETY: `ptr` came from the valid reference passed to
            // `Self::new`. The `PhantomData` in `self.1` has the appropriate
            // lifetime to ensure the reference is still valid, and this method
            // takes ownership of `self` to ensure the data cannot be aliased.
            (unsafe { ptr.as_mut() }, tag)
        }

        /// Returns an immutable reborrow of the reference stored by the tagged
        /// reference.
        ///
        /// See [`Self::get_mut_ref`] if you need a mutable reference.
        pub fn get_ref(&self) -> &T {
            self.get().0
        }

        /// Returns a mutable reborrow of the reference stored by the tagged
        /// reference.
        pub fn get_mut_ref(&mut self) -> &mut T {
            self.get_mut().0
        }

        /// Gets the reference stored by the tagged reference with its original
        /// lifetime (`'a`), consuming the tagged reference in the process.
        ///
        /// Equivalent to <code>[Self::into_inner]().0</code>.
        pub fn into_ref(self) -> &'a mut T {
            self.into_inner().0
        }

        /// Sets the reference without modifying the tag.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
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
            *self = self.with_ref(reference);
        }

        /// Creates a new tagged reference with the same tag but a different
        /// reference.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
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
            TaggedMutRef::new(reference, self.tag())
        }

        /// Gets the tag stored by the tagged reference. Equivalent to
        /// [`self.get().1`](Self::get).
        pub fn tag(&self) -> usize {
            self.get().1
        }

        /// Sets the tag without modifying the reference.
        ///
        /// This method behaves like the following, but it doesn't require
        /// ownership of the tagged reference:
        ///
        /// ```compile_fail
        #[doc = $doctest_context]
        /// # trait Ext<T> { fn f(&mut self, tag: usize); }
        /// # impl<T> Ext<T> for TaggedMutRef<'_, T> {
        /// # fn f(&mut self, tag: usize) {
        /// // Error: can't call `into_ref` on `&mut Self`.
        /// *self = Self::new(self.into_ref(), tag);
        /// # }}
        /// ```
        pub fn set_tag(&mut self, tag: usize) {
            // SAFETY: `self` is a valid reference, so it's safe to read from
            // it, but because `Self` is not `Copy`, we must ensure it isn't
            // accessed until another value is written to it with `ptr::write`.
            // (Conceptually, we're temporarily taking ownership of `*self`.)
            let this = unsafe { ptr::read(self) };
            let this = Self::new(this.into_ref(), tag);
            // SAFETY: `self` is a mutable reference, so it is necessarily
            // aligned and valid for writes.
            unsafe {
                ptr::write(self, this);
            }
        }

        /// Creates a new tagged reference that reborrows the referenced data
        /// with a different lifetime.
        ///
        /// This method is equivalent to:
        ///
        /// ```
        #[doc = $doctest_context]
        /// # trait Ext<T> { fn f(&mut self) -> TaggedMutRef<'_, T>; }
        /// # impl<T> Ext<T> for TaggedMutRef<'_, T> {
        /// # fn f(&mut self) -> TaggedMutRef<'_, T> {
        /// let (reference, tag) = self.get_mut();
        /// TaggedMutRef::new(reference, tag);
        /// # }}
        /// ```
        pub fn reborrow(&mut self) -> TaggedMutRef<'_, $($ty_args)*> {
            let (reference, tag) = self.get_mut();
            TaggedMutRef::new(reference, tag)
        }
    };
}

impl_explicit_tagged_ref_common!(TaggedMutRef);
impl_tagged_mut_ref_common!(
    [T, const BITS: Bits],
    [T, BITS],
    "# type TaggedMutRef<'a, T> = tagged_pointer::TaggedMutRef<'a, T, 0>;",
);

pub mod implied;
