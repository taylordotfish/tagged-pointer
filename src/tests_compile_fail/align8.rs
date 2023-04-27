//@ error-pattern:alignment of `T` must be greater or equal to `BITS`

// If the test fails here with E0464, run `cargo clean` and try again.
extern crate tagged_pointer;
use tagged_pointer::TaggedPtr;

#[repr(align(8))]
#[derive(Debug, Eq, PartialEq)]
struct Align8(pub u64);

fn main() {
    TaggedPtr::<_, 4>::new((&Align8(0)).into(), 0);
}
