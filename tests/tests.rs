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

#![allow(clippy::undocumented_unsafe_blocks)]

use core::ptr::NonNull;
use tagged_pointer::{TaggedMutRef, TaggedPtr, TaggedRef};

#[repr(align(2))]
#[derive(Debug, Eq, PartialEq)]
struct Align2(pub u16);

#[repr(align(4))]
#[derive(Debug, Eq, PartialEq)]
struct Align4(pub u32);

#[repr(align(8))]
#[derive(Debug, Eq, PartialEq)]
struct Align8(pub u64);

const IS_IMPLIED: bool = false;
mod common;

#[path = "."]
mod implied {
    use super::{Align2, Align4, Align8};
    use tagged_pointer::implied;
    type TaggedPtr<T, const N: usize> = implied::TaggedPtr<T>;
    type TaggedRef<'a, T, const N: usize> = implied::TaggedRef<'a, T>;
    type TaggedMutRef<'a, T, const N: usize> = implied::TaggedMutRef<'a, T>;
    const IS_IMPLIED: bool = true;
    #[allow(clippy::duplicate_mod)]
    mod common;
}

#[test]
fn not_entirely_dereferenceable() {
    #[repr(align(8))]
    #[allow(dead_code)]
    struct Type(u64, u64, u64);

    let a = Type(1, 2, 3);
    let mut tp = TaggedPtr::<_, 2>::new((&a).into(), 0b10);
    assert_eq!(tp.get(), ((&a).into(), 0b10));

    let mut b = Align4(0);
    let ptr = NonNull::from(&mut b).cast();
    tp.set_ptr(ptr);
    assert_eq!(tp.ptr(), ptr);
    tp.set_tag(0b11);
    assert_eq!(tp.tag(), 0b11);
    unsafe { tp.ptr().cast::<Align4>().as_mut() }.0 = 1234;
    assert_eq!(b.0, 1234);
}
