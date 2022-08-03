// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

//#[derive(PartialEq)]
enum List2 {
    Cons(i32, Box<List2>), 
    Nil,
}

//#[ensures(result)]
/*fn test_2() {
    let x = List2::Cons(0, Box::new(List2::Nil));
}*/

#[ensures(result)]
fn test(x: List2) -> bool {
    match x{
        List2::Cons(val, _) => false,
        List2::Nil => true,
    }
}

/*
#[ensures(result)]
fn compare(l1: List2, l2: List2) -> bool{
    l1 == l2
}
*/


fn main() {}