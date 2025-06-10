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

use super::IS_IMPLIED;
use super::{Align2, Align4, Align8};
use super::{TaggedMutRef, TaggedPtr, TaggedRef};
use std::mem;
use std::ptr::NonNull;

#[test]
fn basic() {
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
fn basic_ref() {
    for i in 0..64 {
        let x = i as u8 * 3;
        let r = &x;
        let tp = TaggedRef::<_, 0>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (r as *const _, 0));
        assert_eq!(*tp.get_ref(), i as u8 * 3);

        let x = Align2(i as u16 * 5);
        let r = &x;
        let tp = TaggedRef::<_, 1>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (r as *const _, i & 0b1));
        assert_eq!(*tp.get_ref(), Align2(i as u16 * 5));

        let x = Align4(i as u32 * 7);
        let r = &x;
        let tp = TaggedRef::<_, 2>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (r as *const _, i & 0b11));
        assert_eq!(*tp.get_ref(), Align4(i as u32 * 7));

        let x = Align8(i as u64 * 11);
        let r = &x;
        let tp = TaggedRef::<_, 3>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (r as *const _, i & 0b111));
        assert_eq!(*tp.get_ref(), Align8(i as u64 * 11));
    }
}

#[test]
fn basic_mut_ref() {
    for i in 0..64 {
        let mut x = i as u8 * 3;
        let r = &mut x;
        let ptr = r as *const _;
        let tp = TaggedMutRef::<_, 0>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (ptr, 0));
        assert_eq!(*tp.get_ref(), i as u8 * 3);

        let mut x = Align2(i as u16 * 5);
        let r = &mut x;
        let ptr = r as *const _;
        let tp = TaggedMutRef::<_, 1>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (ptr, i & 0b1));
        assert_eq!(*tp.get_ref(), Align2(i as u16 * 5));

        let mut x = Align4(i as u32 * 7);
        let r = &mut x;
        let ptr = r as *const _;
        let mut tp = TaggedMutRef::<_, 2>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (ptr, i & 0b11));
        tp.get_mut_ref().0 += 1;
        assert_eq!(x.0, i as u32 * 7 + 1);

        let mut x = Align8(i as u64 * 11);
        let r = &mut x;
        let ptr = r as *const _;
        let tp = TaggedMutRef::<_, 3>::new(r, i);
        let (a, b) = tp.get();
        assert_eq!((a as *const _, b), (ptr, i & 0b111));
        assert_eq!(*tp.get_ref(), Align8(i as u64 * 11));
    }
}

#[test]
fn overaligned() {
    for i in 0..64 {
        let x = Align2(i as u16 * 3);
        let tp = TaggedPtr::<_, 0>::new((&x).into(), i);
        let mask = [0, 0b1][IS_IMPLIED as usize];
        assert_eq!(tp.get(), ((&x).into(), i & mask));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align4(i as u32 * 5);
        let tp = TaggedPtr::<_, 1>::new((&x).into(), i);
        let mask = [0b1, 0b11][IS_IMPLIED as usize];
        assert_eq!(tp.get(), ((&x).into(), i & mask));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align8(i as u64 * 7);
        let tp = TaggedPtr::<_, 2>::new((&x).into(), i);
        let mask = [0b11, 0b111][IS_IMPLIED as usize];
        assert_eq!(tp.get(), ((&x).into(), i & mask));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn zst() {
    for i in 0..8 {
        let x = ();
        let tp = TaggedPtr::<_, 0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
    }
}

#[test]
#[should_panic]
fn runtime_not_aligned_enough() {
    let ptr: *mut Align2 = &mut Align2(0);
    let ptr = unsafe { (ptr as *mut u8).add(1) };
    let ptr = ptr as *mut Align2;
    let ptr = unsafe { NonNull::new_unchecked(ptr) };
    TaggedPtr::<_, 1>::new(ptr, 0);
}

#[cfg(not(feature = "fallback"))]
#[test]
fn check_size() {
    assert_eq!(
        mem::size_of::<TaggedPtr<u64, 3>>(),
        mem::size_of::<NonNull<u64>>(),
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
fn past_the_end() {
    let mut x = Align8(123);
    let p = (&mut x as *mut Align8).wrapping_add(1);
    let tp = TaggedPtr::<_, 3>::new(NonNull::new(p).unwrap(), 0b101);

    let (p2, t) = tp.get();
    assert_eq!(t, 0b101);

    let p2 = p2.as_ptr().wrapping_sub(1);
    unsafe { &mut *p2 }.0 = 456;
    assert_eq!(x.0, 456);
}

#[test]
fn dangling() {
    let p = NonNull::<Align8>::dangling();
    let tp = TaggedPtr::<_, 3>::new(p, 0b101);

    let (p2, t) = tp.get();
    assert_eq!(p2, p);
    assert_eq!(t, 0b101);
}
