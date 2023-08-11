// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// ignore-test: prusti-constract functions used outside specification check not yet implemented
#[requires(time_credits(50))]
#[ensures(time_receipts(10))]
fn main() {
    let c = time_credits(42); //~ ERROR
    let r = time_receipts(10); //~ ERROR
}
