// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

//a counterexample can only be generated for directly accessed elements of a sequence

fn test1() {
    let mut a = [1; 2];
    a[0] = 2;
    assert!(a[1] == 2);
}

fn test2() {
    let a = [1; 10]; 
    //This is an exception. Here a counterexample contains all elements of the array 
    //as long as no elements is directly accessed. This works only with this syntax.
    assert!(false)
}

#[ensures(result)]
fn test3() -> bool {
    let a = [1, 2, 3, 4];
    a[0] == a[1]   
}

fn main() {}
