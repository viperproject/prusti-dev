// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

//better testcases should be added once raw pointers 
//are implemented in the refactored version
#[ensures(false)]
fn box_test(x: Box<i32>) {
    let y = Box::new(x);
}


fn main(){}