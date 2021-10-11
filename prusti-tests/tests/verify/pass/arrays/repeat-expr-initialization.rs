// this tests
//
// - repeat expressions [{const}; {count}], which look a little different in MIR than regular
//   initializers like [1, 2, 3]
// - bool as element type

extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B([A; 16]);

impl B {
    #[pure]
    /// Initialization of an array holding ADTs.
    pub fn new() -> Self {
        Self([A(0); 16])
    }
}

fn main() {
    let a = [false; 3];

    assert!(a[0] == false);
    assert!(a[1] == false);
    assert!(a[2] == false);
}
