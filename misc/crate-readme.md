tagged-pointer
==============

This crate provides an implementation of [tagged pointers]: a
space-efficient representation of a pointer and integer tag. In particular,
both [`TaggedPtr`] and [`Option<TaggedPtr>`] are the size of a pointer
despite containing both a pointer and tag.

[tagged pointers]: https://en.wikipedia.org/wiki/Tagged_pointer

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
assert_eq!(size_of::<TaggedPtr<Item, 2>>(), size_of::<*mut ()>());
assert_eq!(size_of::<Option<TaggedPtr<Item, 2>>>(), size_of::<*mut ()>());

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

Platform considerations
-----------------------

The number of tag bits that can be stored in a pointer of a given type
depends on the type’s alignment. However, the alignment of many types is
[platform-specific][primitive-layout]: `u64`, for example, could have an
alignment of 8 on one platform and 4 on another.

Therefore, it is highly recommended to use [`#[repr(align)]`][repr-align]
to guarantee a minimum alignment, defining a wrapper type if necessary:

```rust
// This won't work on systems where `u64` has an alignment of 4!
let x: u64 = 123;
let tp = TaggedPtr::<u64, 3>::new(NonNull::from(&x), 0b11);

// Instead, do this:
#[repr(align(8))]
struct MyU64(pub u64);

let x = MyU64(123);
let tp = TaggedPtr::<MyU64, 3>::new(NonNull::from(&x), 0b11);
```

[primitive-layout]:
 https://doc.rust-lang.org/reference/type-layout.html#primitive-data-layout
[repr-align]:
 https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers

Assumptions
-----------

This crate avoids making assumptions about the representations of pointers.
In particular, it does not cast pointers to `usize` and assume that the
lower bits of that number can be used for tagging. There exist
architectures that do not allow reusing the lower bits of aligned pointers
in this manner, and even if none are currently supported by Rust, that
could change in the future. This crate’s approach also works better with
[strict provenance].

[strict provenance]: https://github.com/rust-lang/rust/issues/95228

Previously, this crate relied on assumptions about the behavior of
[`pointer::align_offset`][align_offset] in certain circumstances. These
assumptions were effectively always true, but were not strictly guaranteed,
so a fallback implementation was provided with the crate feature
`fallback`, which would avoid relying on this assumption at the cost of
space efficiency.

However, as of Rust 1.78, this assumption is no longer necessary:
`align_offset` is [guaranteed to behave as required][121201].

[align_offset]:
 https://doc.rust-lang.org/std/primitive.pointer.html#method.align_offset
[121201]: https://github.com/rust-lang/rust/pull/121201/

[`TaggedPtr`]: https://docs.rs/tagged-pointer/0.2/tagged_pointer/struct.TaggedPtr.html
[`Option<TaggedPtr>`]: https://doc.rust-lang.org/std/option/enum.Option.html
