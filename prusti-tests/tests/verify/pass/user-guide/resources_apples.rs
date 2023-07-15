//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
#[derive(Clone, Copy)]
enum Currency {
    CAD,
    CHF,
    DKK,
}

resource! {
    fn cash(amount: usize, currency: Currency);
}

resource! {
    fn apples(amount: usize);
}

#[trusted]
#[requires(cash(2, Currency::CHF))]
#[ensures(apples(1))]
fn buy_apple() {
    // buy an apple in the real world
}

#[trusted]
#[requires(cash(2, Currency::CAD))]
#[ensures(cash(1, Currency::CHF))]
fn exchange() {
    // perform a currency exchange in the real world
}

#[requires(cash(4, Currency::CAD))]
#[ensures(apples(1))]
fn buy_apple_in_canada() {
    exchange();
    exchange();
    buy_apple();
}
//// ANCHOR_END: code
