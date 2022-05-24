// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


//#[derive(Copy, Clone)]
enum X{
    One(Y, i32),
    Two,
}
enum Y{
    One(i32),
    Two,
}


#[ensures(result)]
fn test(x: X) -> bool{
   match x{
       X::One(_, _) => true,
       X::Two => false,
   }
}


fn main() {}