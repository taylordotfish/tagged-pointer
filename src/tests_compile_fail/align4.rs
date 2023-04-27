//@ error-pattern:alignment of `T` must be greater or equal to `BITS`

// If the test fails here with E0464, run `cargo clean` and try again.
extern crate tagged_pointer;
use tagged_pointer::TaggedPtr;

#[repr(align(4))]
#[derive(Debug, Eq, PartialEq)]
struct Align4(pub u32);

fn main() {
    TaggedPtr::<_, 3>::new((&Align4(0)).into(), 0);
}
