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

fn f1() {
    prusti_exhale!(o(1)); //~ ERROR there might be not enough resources for the exhale
}

#[requires(o(2))]
#[ensures(o(2))]
fn f2() { //~ ERROR function might leak instances of obligation `o`
    prusti_inhale!(o(2));
}
//// ANCHOR_END: code
