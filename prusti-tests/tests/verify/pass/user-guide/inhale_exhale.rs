//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
obligation! {
    fn o(amount: usize);
}

#[requires(o(3))]
fn f1() {
    prusti_exhale!(o(3));
}

#[requires(o(3))]
fn f2() {
    prusti_exhale!(o(1) & o(1));
    prusti_exhale!(o(1));
}

#[requires(o(1))]
#[ensures(o(3))]
fn f3() {
    prusti_inhale!(o(1));
    prusti_inhale!(o(1));
}
//// ANCHOR_END: code
