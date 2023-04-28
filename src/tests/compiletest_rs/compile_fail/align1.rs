//@ error-pattern:alignment of `T` must be at least `1 << BITS`

// If the test fails here with E0464, run `cargo clean` and try again.
extern crate tagged_pointer;
use tagged_pointer::TaggedPtr;

fn main() {
    TaggedPtr::<_, 1>::new((&0_u8).into(), 0);
}
