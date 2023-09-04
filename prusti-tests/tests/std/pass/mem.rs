use prusti_contracts::*;

use core::mem::{align_of, size_of};

fn main() {
    assert!(size_of::<[i32; 3]>() == 12);
    assert!(align_of::<[i32; 3]>() == 4);
    assert!(size_of::<Foo>() == 8);
    assert!(align_of::<Foo>() == 4);
}

struct Foo {
    a: i32,
    b: i32,
}

impl core_spec::KnownSize for Foo {
    #[pure]
    fn size() -> usize {
        8
    }

    #[pure]
    fn align() -> usize {
        4
    }
}
