#![feature(negative_impls)]

use prusti_contracts::*;

fn main() {}

fn numeric_conversions() {
    let small: u8 = 42;
    let x = 42;
    assert!(i32::from(small) == x);
    let converted: i32 = small.into();
    assert!(converted == x);
}

fn self_conversion() {
    let foo = Foo { x: 42 };
    let converted: Foo = foo.into();
    assert!(converted.x == foo.x);
}

#[derive(Clone, Copy)]
struct Foo {
    x: i32,
}

fn impure_conversion() {
    let x = 42;
    let converted = ImpureFrom::from(x);
    assert!(converted.x == 1);
}

#[derive(Clone, Copy)]
struct ImpureFrom {
    x: i32,
}

impl !core_spec::PureFrom for ImpureFrom {}

#[refine_trait_spec]
impl From<i32> for ImpureFrom {
    #[ensures(result.x == 1)]
    #[trusted]
    fn from(x: i32) -> Self {
        Self { x }
    }
}

// can't currently specify blanket Into impl for impure types
fn impure_self_conversion() {
    let unique = Unique { x: 1 };
    let converted = Unique::from(unique);
    assert!(converted.x == 1);
}

struct Unique {
    x: i32,
}
