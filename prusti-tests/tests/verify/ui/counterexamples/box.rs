// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[ensures(!result)]
fn box_test(x: i32) -> bool {
    let y = Box::new(x);
    let z = Box::new(y);
    **z == 0
}


fn main(){}