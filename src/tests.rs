/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * tagged-pointer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with tagged-pointer. If not, see <https://www.gnu.org/licenses/>.
 */

use super::TaggedPtr;
#[allow(clippy::wildcard_imports)]
use typenum::consts::*;

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
        let tp = TaggedPtr::<_, U0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align2(i as u16 * 5);
        let tp = TaggedPtr::<_, U1>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align4(i as u32 * 7);
        let tp = TaggedPtr::<_, U2>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b11));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align8(i as u64 * 11);
        let tp = TaggedPtr::<_, U3>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b111));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn overaligned() {
    #![allow(clippy::cast_possible_truncation)]
    for i in 0..64 {
        let x = Align2(i as u16 * 3);
        let tp = TaggedPtr::<_, U0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align4(i as u32 * 5);
        let tp = TaggedPtr::<_, U1>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b1));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);

        let x = Align8(i as u64 * 7);
        let tp = TaggedPtr::<_, U2>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), i & 0b11));
        assert_eq!(*unsafe { tp.ptr().as_ref() }, x);
    }
}

#[test]
fn zst() {
    #![allow(clippy::let_unit_value)]
    for i in 0..8 {
        let x = ();
        let tp = TaggedPtr::<_, U0>::new((&x).into(), i);
        assert_eq!(tp.get(), ((&x).into(), 0));
    }
}

mod not_aligned_enough {
    use super::*;

    #[test]
    #[should_panic]
    fn test1() {
        TaggedPtr::<_, U1>::new((&0_u8).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test2() {
        TaggedPtr::<_, U2>::new((&Align2(0)).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test3() {
        TaggedPtr::<_, U3>::new((&Align4(0)).into(), 0);
    }

    #[test]
    #[should_panic]
    fn test4() {
        TaggedPtr::<_, U4>::new((&Align8(0)).into(), 0);
    }
}

#[cfg(not(feature = "fallback"))]
#[test]
fn check_size() {
    assert_eq!(
        core::mem::size_of::<TaggedPtr<u64, U3>>(),
        core::mem::size_of::<core::ptr::NonNull<u64>>(),
    );
}

#[test]
fn check_option_size() {
    assert_eq!(
        core::mem::size_of::<TaggedPtr<u64, U3>>(),
        core::mem::size_of::<Option<TaggedPtr<u64, U3>>>(),
    );
}

/// The example from the crate documentation. It's duplicated here because Miri
/// currently doesn't run doctests.
#[test]
fn crate_example() {
    #[cfg(not(feature = "fallback"))]
    use core::mem::size_of;
    use core::ptr::NonNull;

    #[repr(align(4))]
    struct Item(u32, u32);

    #[cfg(not(feature = "fallback"))]
    {
        // `TaggedPtr` and `Option<TaggedPtr>` are both the size of a pointer:
        assert_eq!(size_of::<TaggedPtr<Item, U2>>(), size_of::<usize>());
        assert_eq!(
            size_of::<Option<TaggedPtr<Item, U2>>>(),
            size_of::<usize>()
        );
    }

    let item1 = Item(1, 2);
    let item2 = Item(3, 4);

    // We can store two bits of the tag, since `Item` has an alignment of 4.
    let tp1 = TaggedPtr::<_, U2>::new(NonNull::from(&item1), 1);
    let tp2 = TaggedPtr::<_, U2>::new(NonNull::from(&item2), 3);

    let (ptr1, tag1) = tp1.get();
    let (ptr2, tag2) = tp2.get();

    assert_eq!((ptr1, tag1), (NonNull::from(&item1), 1));
    assert_eq!((ptr2, tag2), (NonNull::from(&item2), 3));
}
