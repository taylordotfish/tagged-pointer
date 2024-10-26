use crate::Bits;

#[macro_use]
pub mod implied;

macro_rules! impl_explicit_tagged_ref_common {
    ($name:ident) => {
        impl<T, const BITS: Bits> $name<'_, T, BITS> {
            /// The number of tag bits that this tagged reference can store.
            pub const BITS: u32 = BITS;

            /// The maximum tag (inclusive) that this tagged reference can
            /// store. Equal to `(1 << BITS) - 1` (i.e., one less than 2 to the
            /// power of `BITS`).
            pub const MAX_TAG: usize = crate::TaggedPtr::<T, BITS>::MAX_TAG;
        }
    };
}

pub struct TaggedRef<'a, T, const BITS: Bits>(implied::TaggedRef<'a, T>);

impl<'a, T, const BITS: Bits> TaggedRef<'a, T, BITS> {
    /// Creates a new tagged reference. Only the lower [`BITS`] bits of `tag`
    /// are stored.
    pub fn new(reference: &'a T, tag: usize) -> Self {
        crate::TaggedPtr::<T, BITS>::assert();
        let tag = tag & Self::MAX_TAG;
        // SAFETY: `tag` cannot be greater than `Self::MAX_TAG` after the
        // bitwise-and, and `Self::MAX_TAG` must be less than or equal to
        // `implied::TaggedRef::<'a, T>::MAX_TAG`, due to the compile-time
        // `TaggedPtr<T, BITS>` checks.
        Self(unsafe { implied::TaggedRef::new_unchecked(reference, tag) })
    }

    /// Equivalent to [`Self::new`] but without some runtime checks.
    ///
    /// # Safety
    ///
    /// `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(reference: &'a T, tag: usize) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { implied::TaggedRef::new_unchecked(reference, tag) })
    }
}

impl_explicit_tagged_ref_common!(TaggedRef);
impl_tagged_ref_common!(
    [T, const BITS: Bits],
    [T, BITS],
    is_wrapper: cfg(all()),
    "# type TaggedRef<'a, T> = tagged_pointer::TaggedRef<'a, T, 0>;",
);

pub struct TaggedMutRef<'a, T, const BITS: Bits>(implied::TaggedMutRef<'a, T>);

impl<'a, T, const BITS: Bits> TaggedMutRef<'a, T, BITS> {
    /// Creates a new tagged mutable reference. Only the lower [`BITS`] bits of
    /// `tag` are stored.
    pub fn new(reference: &'a mut T, tag: usize) -> Self {
        crate::TaggedPtr::<T, BITS>::assert();
        let tag = tag & Self::MAX_TAG;
        // SAFETY: `tag` cannot be greater than `Self::MAX_TAG` after the
        // bitwise-and, and `Self::MAX_TAG` must be less than or equal to
        // `implied::TaggedMutRef::<'a, T>::MAX_TAG`, due to the compile-time
        // `TaggedPtr<T, BITS>` checks.
        Self(unsafe { implied::TaggedMutRef::new_unchecked(reference, tag) })
    }

    /// Equivalent to [`Self::new`] but without some runtime checks.
    ///
    /// # Safety
    ///
    /// `tag` cannot be greater than [`Self::MAX_TAG`].
    pub unsafe fn new_unchecked(reference: &'a mut T, tag: usize) -> Self {
        // SAFETY: Ensured by caller.
        Self(unsafe { implied::TaggedMutRef::new_unchecked(reference, tag) })
    }
}

impl_explicit_tagged_ref_common!(TaggedMutRef);
impl_tagged_mut_ref_common!(
    [T, const BITS: Bits],
    [T, BITS],
    is_wrapper: cfg(all()),
    "# type TaggedMutRef<'a, T> = tagged_pointer::TaggedMutRef<'a, T, 0>;",
);
