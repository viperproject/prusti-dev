// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


#[requires(y.0 == y.1)]
#[ensures(result)]
fn test(x: (i32, i32), y:(i32, i32)) -> bool{
    x.0 == x.1
}


fn main() {}