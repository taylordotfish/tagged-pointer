/*
 * Copyright 2021-2022 taylor.fish <contact@taylor.fish>
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

use super::TaggedPtr;
use core::mem;
use core::ptr::NonNull;

#[repr(align(2))]
#[derive(Debug, Eq, PartialEq)]
struct Align2(pub u16);

#[repr(align(4))]
#[derive(Debug, Eq, PartialEq)]
struct Align4(pub u32);

#[repr(align(8))]
#[derive(Debug, Eq, PartialEq)]
struct Align8(pub u64);

#[test]
fn basic() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let x = i as u8 * 3;
        let tp = TaggedPtr::<_, 0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align2(i as u16 * 5);
        let tp = TaggedPtr::<_, 1>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let mut x = Align4(i as u32 * 7);
        let ptr = NonNull::from(&mut x);
        let tp = TaggedPtr::<_, 2>::new(ptr, i);
        assert_eq!(tp.get(), (ptr, i & 0b11));
        unsafe { tp.ptr().as_mut() }.0 += 1;
        assert_eq!(x.0, i as u32 * 7 + 1);

        let x = Align8(i as u64 * 11);
        let tp = TaggedPtr::<_, 3>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b111));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn overaligned() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let x = Align2(i as u16 * 3);
        let tp = TaggedPtr::<_, 0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align4(i as u32 * 5);
        let tp = TaggedPtr::<_, 1>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align8(i as u64 * 7);
        let tp = TaggedPtr::<_, 2>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b11));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn zst() {
    #![allow(clippy::let_unit_value)]
    for i in 0..8 {
        let x = ();
        let tp = TaggedPtr::<_, 0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
    }
}

mod not_aligned_enough {
    use super::*;

    #[test]
    #[should_panic]
    fn test1() {
        TaggedPtr::<_, 1>::new((&0_u8).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test2() {
        TaggedPtr::<_, 2>::new((&Align2(0)).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test3() {
        TaggedPtr::<_, 3>::new((&Align4(0)).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test4() {
        TaggedPtr::<_, 4>::new((&Align8(0)).into(), 0);
    }
}

#[cfg(not(feature = "fallback"))]
#[test]
fn check_size() {
    assert_eq!(
        mem::size_of::<TaggedPtr<u64, 3>>(),
        mem::size_of::<core::ptr::NonNull<u64>>(),
    );
}

#[test]
fn check_option_size() {
    assert_eq!(
        mem::size_of::<TaggedPtr<u64, 3>>(),
        mem::size_of::<Option<TaggedPtr<u64, 3>>>(),
    );
}

#[test]
fn not_entirely_dereferencable() {
    #[repr(align(8))]
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
