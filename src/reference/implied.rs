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
use crate::implied::TaggedPtr;

macro_rules! impl_implied_tagged_ref_common {
    ($name:ident $(,)?) => {
        impl<T> $name<'_, T> {
            /// The number of tag bits that this tagged reference can store.
            pub const BITS: u32 = TaggedPtr::<T>::BITS;

            /// The maximum tag (inclusive) that this tagged reference can
            /// store. Equal to <code>[mem::align_of]::\<T>() - 1</code>.
            ///
            /// [mem::align_of]: core::mem::align_of
            pub const MAX_TAG: usize = TaggedPtr::<T>::MAX_TAG;
        }
    };
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
        Self::new_impl(reference, tag)
    }
}

impl_implied_tagged_ref_common!(TaggedRef);
impl_tagged_ref_common!(
    [T],
    [T],
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
        Self::new_impl(reference, tag)
    }
}

impl_implied_tagged_ref_common!(TaggedMutRef);
impl_tagged_mut_ref_common!(
    [T],
    [T],
    "# use tagged_pointer::implied::TaggedMutRef;",
);
