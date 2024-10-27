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

use super::{TaggedMutRef, TaggedPtr, TaggedRef};
use core::mem;
use core::ptr::NonNull;

#[cfg(not(doctest))]
#[cfg(compiletest_rs)]
mod compiletest_rs;

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
        let tp = TaggedPtr::new::<0>((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align2(i as u16 * 5);
        let tp = TaggedPtr::new::<1>((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let mut x = Align4(i as u32 * 7);
        let ptr = NonNull::from(&mut x);
        let tp = TaggedPtr::new::<2>(ptr, i);
        assert_eq!(tp.get(), (ptr, i & 0b11));
        unsafe { tp.ptr().as_mut() }.0 += 1;
        assert_eq!(x.0, i as u32 * 7 + 1);

        let x = Align8(i as u64 * 11);
        let tp = TaggedPtr::new::<3>((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b111));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn basic_ref() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let x = i as u8 * 3;
        let r = &x;
        let addr = r as *const _ as usize;
        let tp = TaggedRef::new::<0>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, 0));
        assert_eq!(*tp.reference(), i as u8 * 3);

        let x = Align2(i as u16 * 5);
        let r = &x;
        let addr = r as *const _ as usize;
        let tp = TaggedRef::new::<1>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b1));
        assert_eq!(*tp.reference(), Align2(i as u16 * 5));

        let x = Align4(i as u32 * 7);
        let r = &x;
        let addr = r as *const _ as usize;
        let tp = TaggedRef::new::<2>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b11));
        assert_eq!(*tp.reference(), Align4(i as u32 * 7));

        let x = Align8(i as u64 * 11);
        let r = &x;
        let addr = r as *const _ as usize;
        let tp = TaggedRef::new::<3>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b111));
        assert_eq!(*tp.reference(), Align8(i as u64 * 11));
    }
}

#[test]
fn basic_mut_ref() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let mut x = i as u8 * 3;
        let r = &mut x;
        let addr = r as *const _ as usize;
        let tp = TaggedMutRef::new::<0>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, 0));
        assert_eq!(*tp.reference(), i as u8 * 3);

        let mut x = Align2(i as u16 * 5);
        let r = &mut x;
        let addr = r as *const _ as usize;
        let tp = TaggedMutRef::new::<1>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b1));
        assert_eq!(*tp.reference(), Align2(i as u16 * 5));

        let mut x = Align4(i as u32 * 7);
        let r = &mut x;
        let addr = r as *const _ as usize;
        let mut tp = TaggedMutRef::new::<2>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b11));
        tp.reference_mut().0 += 1;
        assert_eq!(x.0, i as u32 * 7 + 1);

        let mut x = Align8(i as u64 * 11);
        let r = &mut x;
        let addr = r as *const _ as usize;
        let tp = TaggedMutRef::new::<3>(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _ as usize, b), (addr, i & 0b111));
        assert_eq!(*tp.reference(), Align8(i as u64 * 11));
    }
}

#[test]
fn overaligned() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let x = Align2(i as u16 * 3);
        let tp = TaggedPtr::new::<0>(NonNull::from(&x).cast::<u8>(), i);
        assert_eq!(tp.get(), (NonNull::from(&x).cast::<u8>(), 0));
        assert_eq!(*unsafe { tp.ptr().cast::<Align2>().as_ref() }, x);

        let x = Align4(i as u32 * 5);
        let tp = TaggedPtr::new::<1>(NonNull::from(&x).cast::<Align2>(), i);
        assert_eq!(tp.get(), (NonNull::from(&x).cast::<Align2>(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().cast::<Align4>().as_ref() }, x);

        let x = Align8(i as u64 * 7);
        let tp = TaggedPtr::new::<2>(NonNull::from(&x).cast::<Align4>(), i);
        assert_eq!(tp.get(), (NonNull::from(&x).cast::<Align4>(), i & 0b11));
        assert_eq!(*unsafe { tp.ptr().cast::<Align8>().as_ref() }, x);
    }
}

#[test]
fn zst() {
    #![allow(clippy::let_unit_value)]
    for i in 0..8 {
        let x = ();
        let tp = TaggedPtr::new::<0>((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
    }
}

#[test]
#[cfg_attr(not(feature = "fallback"), should_panic)]
fn runtime_not_aligned_enough() {
    let ptr: *mut Align2 = &mut Align2(0);
    let ptr = unsafe { (ptr as *mut u8).add(1) };
    let ptr = ptr as *mut Align2;
    let ptr = unsafe { NonNull::new_unchecked(ptr) };
    TaggedPtr::new::<1>(ptr, 0);
}

mod type_not_aligned_enough {
    /// ```
    /// use tagged_pointer::TaggedPtr;
    /// TaggedPtr::new::<0>((&0_u8).into(), 0);
    /// ```
    ///
    /// ```compile_fail
    /// use tagged_pointer::TaggedPtr;
    /// TaggedPtr::new::<1>((&0_u8).into(), 0);
    /// ```
    mod test1 {}

    /// ```
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(2))]
    /// struct Align2(pub u16);
    /// TaggedPtr::new::<1>((&Align2(0)).into(), 0);
    /// ```
    ///
    /// ```compile_fail
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(2))]
    /// struct Align2(pub u16);
    /// TaggedPtr::new::<2>((&Align2(0)).into(), 0);
    /// ```
    mod test2 {}

    /// ```
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(4))]
    /// struct Align4(pub u32);
    /// TaggedPtr::new::<2>((&Align4(0)).into(), 0);
    /// ```
    ///
    /// ```compile_fail
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(4))]
    /// struct Align4(pub u32);
    /// TaggedPtr::new::<3>((&Align4(0)).into(), 0);
    /// ```
    mod test3 {}

    /// ```
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(8))]
    /// struct Align8(pub u64);
    /// TaggedPtr::new::<3>((&Align8(0)).into(), 0);
    /// ```
    ///
    /// ```compile_fail
    /// use tagged_pointer::TaggedPtr;
    /// #[repr(align(8))]
    /// struct Align8(pub u64);
    /// TaggedPtr::new::<4>((&Align8(0)).into(), 0);
    /// ```
    mod test4 {}
}

#[cfg(not(feature = "fallback"))]
#[test]
fn check_size() {
    assert_eq!(
        mem::size_of::<TaggedPtr<u64>>(),
        mem::size_of::<core::ptr::NonNull<u64>>(),
    );
}

#[test]
fn check_option_size() {
    assert_eq!(
        mem::size_of::<TaggedPtr<u64>>(),
        mem::size_of::<Option<TaggedPtr<u64>>>(),
    );
}

#[test]
fn not_entirely_dereferenceable() {
    #[allow(dead_code)]
    #[repr(align(8))]
    struct Type(u64, u64, u64);

    let a = Type(1, 2, 3);
    let mut tp = TaggedPtr::new::<2>(NonNull::from(&a).cast::<Align4>(), 0b10);
    assert_eq!(tp.get(), (NonNull::from(&a).cast::<Align4>(), 0b10));

    let mut b = Align4(0);
    let ptr = NonNull::from(&mut b).cast();
    tp.set_ptr(ptr);
    assert_eq!(tp.ptr(), ptr);
    tp.set_tag::<2>(0b11);
    assert_eq!(tp.tag(), 0b11);
    unsafe { tp.ptr().cast::<Align4>().as_mut() }.0 = 1234;
    assert_eq!(b.0, 1234);
}
