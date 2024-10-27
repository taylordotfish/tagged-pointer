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

use crate::implied::TaggedPtr;
use core::marker::PhantomData;

macro_rules! impl_implied_tagged_ref_common {
    ($name:ident $(,)?) => {
        impl<T> $name<'_, T> {
            /// The number of tag bits that this tagged reference can store.
            pub const BITS: u32 = TaggedPtr::<T>::BITS;

            /// The maximum tag (inclusive) that this tagged reference can
            /// store. Equal to <code>[align_of]::\<T>() - 1</code>.
            ///
            /// [align_of]: core::mem::align_of
            pub const MAX_TAG: usize = TaggedPtr::<T>::MAX_TAG;
        }
    };
}

/// A tagged reference with the maximum tag size for the given type.
///
/// This type behaves like [`crate::TaggedRef`] but doesn't have a `BITS`
/// parameter that determines how many tag bits to store. Instead, this type
/// uses the largest possible tag size for a reference to `T`; see
/// [`Self::BITS`] for the exact calculation.
#[repr(transparent)]
pub struct TaggedRef<'a, T>(TaggedPtr<T>, PhantomData<&'a T>);

impl<'a, T> TaggedRef<'a, T> {
    /// Creates a new tagged reference. Only the lower [`Self::BITS`] bits of
    /// `tag` are stored.
    pub fn new(reference: &'a T, tag: usize) -> Self {
        Self::new_impl(reference, tag)
    }
}

impl_implied_tagged_ref_common!(TaggedRef);
impl_tagged_ref_common!([T], [T], "# use tagged_pointer::implied::TaggedRef;");

/// Mutable version of [`TaggedRef`].
///
/// This type behaves like [`crate::TaggedMutRef`] but doesn't have a `BITS`
/// parameter that determines how many tag bits to store. Instead, this type
/// uses the largest possible tag size for a reference to `T`; see
/// [`Self::BITS`] for the exact calculation.
#[repr(transparent)]
pub struct TaggedMutRef<'a, T>(TaggedPtr<T>, PhantomData<&'a mut T>);

impl<'a, T> TaggedMutRef<'a, T> {
    /// Creates a new tagged mutable reference. Only the lower [`Self::BITS`]
    /// bits of `tag` are stored.
    pub fn new(reference: &'a mut T, tag: usize) -> Self {
        Self::new_impl(reference, tag)
    }
}

impl_implied_tagged_ref_common!(TaggedMutRef);
impl_tagged_mut_ref_common!(
    [T],
    [T],
    "# use tagged_pointer::implied::TaggedMutRef;",
);
