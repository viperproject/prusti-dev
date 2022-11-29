// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// ignore-test: prusti-constract functions used outside specification check not yet implemented
fn main() {
    let _i;
    if time_credits(2) && time_receipts(1) {
        //~ ERROR
        _i = 1;
    } else {
        _i = 2;
    }
}
