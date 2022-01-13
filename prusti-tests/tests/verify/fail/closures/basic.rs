// ignore-test

use prusti_contracts::*;

fn main() {
    let f = closure!(
        #[requires(i > 0)]
        #[ensures(true)]
        |i: i32| -> i32 { i }
    );
    f(0); //~ ERROR precondition might not hold
}
