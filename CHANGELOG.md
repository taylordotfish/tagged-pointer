Changelog
=========

0.2.11
------

* Improved error message when `align_offset` doesn't behave as required. This
  should never happen, though, due to the strengthening of `align_offset` in
  Rust 1.78.

0.2.10
------

* Fixed issue where the fallback implementation was not used when enabled.

0.2.9
-----

* Fixed documentation for `implied::TaggedPtr`. It had erroneously stated that
  pointers must be dereferenceable.
* Improved example in crate documentation/README.

0.2.8
-----

* Added tagged reference types.
* Added “implied” tagged pointer types that don't take a `BITS` parameter.
* Removed requirement for pointers to be dereferenceable.
* Added unsafe `new_unchecked` and `new_unchecked_dereferenceable` functions.

Thanks to [@JonasAlaif] for writing the initial version of the tagged reference
and implied types.

0.2.7
-----

* Switched to performing certain safety checks at compile time.

Thanks to [@JonasAlaif] for writing the initial version of this change.

[@JonasAlaif]: https://github.com/JonasAlaif

0.2.6
-----

* Added `rerun-if-changed` to the build script.

0.2.5
-----

* Fixed build script on older Rust versions.

0.2.4
-----

* Added `TaggedPtr::set_ptr` and `TaggedPtr::set_tag`.
* Relaxed the requirement for pointers to be dereferenceable. Now, only
  2<sup>`BITS`</sup> bytes need to be dereferenceable.

0.2.3
-----

* Various code and documentation improvements (no API changes).

0.2.2
-----

* Loosened requirements for `align_offset`'s behavior. When called on an
  already-aligned pointer, it is now acceptable for `align_offset` to return
  any multiple of the requested alignment instead of only 0.

0.2.1
-----

* Relicensed under Apache 2.0.

0.2.0
-----

* Const generics are now used instead of `typenum`.

0.1.1–0.1.3
-----------

* Minor fixes to documentation.

0.1.0
-----

Initial release.
