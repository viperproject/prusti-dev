extern crate prusti_contracts;
use prusti_contracts::*;


struct T {}
struct K<'a> {d: &'a mut T}

#[pure]
fn main() {
    let mut t = T {};
    let k = K {d: &mut t};
    let t0 = t;
}
