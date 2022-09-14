// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test_forall_1() -> usize {
    let res = 5;
    prusti_assert!(
        forall(|x: usize| true) || false
    );
    res
}

fn test_forall_2() -> usize {
    let res = 5;
    prusti_assert!(
        forall(|x: usize| x >= 0)
    );
    res
}

fn test_forall_3() -> usize {
    let res = 5;
    prusti_assert!(
        forall(|x: usize| x >= 1)   //~ ERROR: the asserted expression might not hold
    );
    res
}

fn main() {}
