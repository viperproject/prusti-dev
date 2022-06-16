// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


//#[derive(Copy, Clone)]
#[print_counterexample]
enum X{
    #[print_counterexample("[{}] and [{}]", 0, 1, )]
    One(Y, i32),
    Two,
}

#[print_counterexample]
enum Y{
    One(i32),
    #[print_counterexample("Three")]
    Two,
}


#[ensures(!result)]
fn test(x: X) -> bool{
   match x{
       X::One(_, i) => i == 0,
       X::Two => false,
   }
}


fn main() {}