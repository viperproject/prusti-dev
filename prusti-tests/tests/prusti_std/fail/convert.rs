#![feature(negative_impls)]

use prusti_contracts::*;

fn main() {}

fn numeric_conversions_1() {
    let small: u8 = 41;
    let x = 42;
    assert!(i32::from(small) == x); //~ ERROR the asserted expression might not hold
}

fn numeric_conversions_2() {
    let small: u8 = 41;
    let x = 42;
    let converted: i32 = small.into();
    assert!(converted == x); //~ ERROR the asserted expression might not hold
}

fn impure_conversion() {
    let x = 42;
    let converted = ImpureFrom::from(x);
    assert!(converted.x == 1);
    // because our from implementation is not pure, it can't be used to express the behavior of into:
    let converted: ImpureFrom = x.into();
    assert!(converted.x == 1); //~ ERROR the asserted expression might not hold
}

#[derive(Clone, Copy)]
struct ImpureFrom {
    x: i32,
}

impl !core_spec::convert::PureFrom for ImpureFrom {}

#[refine_trait_spec]
impl From<i32> for ImpureFrom {
    #[ensures(result.x == 1)]
    #[trusted]
    fn from(x: i32) -> Self {
        Self { x }
    }
}
