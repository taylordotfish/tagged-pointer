//@ error-pattern:alignment of `T` must be at least `1 << BITS`

// If the test fails here with E0464, run `cargo clean` and try again.
extern crate tagged_pointer;
use tagged_pointer::TaggedPtr;

#[repr(align(2))]
#[derive(Debug, Eq, PartialEq)]
struct Align2(pub u16);

fn main() {
    TaggedPtr::<_, 2>::new((&Align2(0)).into(), 0);
}
