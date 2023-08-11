//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
resource! {
    fn rsrc(amount: usize);
}

obligation! {
    fn oblg(amount: usize);
}

#[requires(rsrc(3))]
#[ensures(rsrc(2))]
fn with_resources() {
    // does nothing
}

#[requires(oblg(3))]
#[ensures(oblg(2))]
fn with_obligations() { //~ ERROR function might leak instances of obligation `oblg`
    // does nothing
}
//// ANCHOR_END: code
