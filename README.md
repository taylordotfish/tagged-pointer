tagged-pointer
==============

This crate provides an implementation of [tagged pointers]: pointers that
also contain an integer tag in a space-efficient manner.

[tagged pointers]: https://en.wikipedia.org/wiki/Tagged_pointer

Unless the fallback implementation is used (see the
[Assumptions](#assumptions) section below), both [`TaggedPtr`] and
[`Option<TaggedPtr>`] are guaranteed to be the size of a pointer.

This crate depends only on [`core`], so it can be used in `no_std`
environments.

[`core`]: https://doc.rust-lang.org/core/

Example
-------

```rust
use core::mem::size_of;
use core::ptr::NonNull;
use tagged_pointer::TaggedPtr;

#[repr(align(4))]
struct Item(u32, u32);

// `TaggedPtr` and `Option<TaggedPtr>` are both the size of a pointer:
assert_eq!(size_of::<TaggedPtr<Item, 2>>(), size_of::<usize>());
assert_eq!(size_of::<Option<TaggedPtr<Item, 2>>>(), size_of::<usize>());

let item1 = Item(1, 2);
let item2 = Item(3, 4);

// We can store two bits of the tag, since `Item` has an alignment of 4.
let tp1 = TaggedPtr::<_, 2>::new(NonNull::from(&item1), 1);
let tp2 = TaggedPtr::<_, 2>::new(NonNull::from(&item2), 3);

let (ptr1, tag1) = tp1.get();
let (ptr2, tag2) = tp2.get();

assert_eq!((ptr1, tag1), (NonNull::from(&item1), 1));
assert_eq!((ptr2, tag2), (NonNull::from(&item2), 3));
```

Assumptions
-----------

This crate relies on [`pointer::align_offset`][`align_offset`] not failing
under certain circumstances. Specifically, [`align_offset`], when called in
a non-const context on a pointer to [`u8`], must succeed when the desired
alignment is less than or equal to the alignment of the allocation pointed
to by the provided pointer. In practice, this is true, even in [Miri] with
the `-Zmiri-symbolic-alignment-check` flag, but the specifications of
[`align_offset`] technically allow an implementation not to follow this
behavior. If you experience issues due to this, please file an issue in the
[Git repository]. As a workaround, you can enable the `fallback` feature,
which avoids relying on [`align_offset`] at the cost of making
[`TaggedPtr`] twice as large.

[Miri]: https://github.com/rust-lang/miri

Note that this crate is always sound: an implementation of [`align_offset`]
that doesn’t follow the required behavior may cause panics, but not
undefined behavior.

[`align_offset`]:
https://doc.rust-lang.org/std/primitive.pointer.html#method.align_offset
[Git repository]: https://github.com/taylordotfish/tagged-pointer

Unfortunately, there’s currently no way to implement space-efficient tagged
pointers in Rust without making some assumptions. However, this approach
has some advantages over the usual method of casting the pointer to a
[`usize`] and reusing the lower bits: the usual approach makes
platform-specific assumptions about the representation of pointers (which
currently apply to all platforms supported by rustc but could be
invalidated if support for new architectures is added, and there are
real architectures which do not allow reusing the lower bits of aligned
pointers), whereas this crate’s assumptions are platform-independent (aside
from the requirements already imposed by Rust, like having 8-bit bytes) and
are satisfied by all known implementations of Rust, including Miri with
`-Zmiri-symbolic-alignment-check`.

[`TaggedPtr`]: https://docs.rs/tagged-pointer/latest/tagged_pointer/struct.TaggedPtr.html
[`Option<TaggedPtr>`]: https://doc.rust-lang.org/std/option/enum.Option.html
[`u8`]: https://doc.rust-lang.org/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/std/primitive.usize.html

Documentation
-------------

[Documentation is available on docs.rs.](https://docs.rs/tagged-pointer)

License
-------

tagged-pointer is licensed under version 2 of the Apache License. See
[LICENSE](LICENSE).

Contributing
------------

By contributing to tagged-pointer, you agree that your contribution may be used
according to the terms of tagged-pointer’s license.
