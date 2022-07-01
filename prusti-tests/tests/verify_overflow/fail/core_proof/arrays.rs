// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=2000 -Psmt_quantifier_instantiations_bound_trace_kind=150 -Psmt_quantifier_instantiations_bound_global_kind=150

use prusti_contracts::*;

fn test1() {
    let a = [1, 2];
}

fn test2() {
    let a = [1, 2];
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

fn test3() {
    let a = [1; 100];
}

fn test4() {
    let a = [1; 100];
    let b = a[1];
    assert!(b == 1);
}

fn test5() {
    let a = [1; 100];
    let b = a[1];
    assert!(b == 6);     //~ ERROR: the asserted expression might not hold
}

fn test6() {
    let a = [1; 100];
    let b = a[1];
    let c = a[2];
    assert!(b == 1);
    assert!(c == 1);
}

fn test7() {
    let a = [1; 100];
    let b = a[1];
    let c = a[2];
    assert!(b == 1);
    assert!(c == 2);     //~ ERROR: the asserted expression might not hold
}

fn test10() {
    let mut a = [1; 100];
    a[1] = 2;
    prusti_assert!(a[1] == 2);
    prusti_assert!(a[0] == 1);
    prusti_assert!(a[2] == 1);
    prusti_assert!(a[3] == 1);
    prusti_assert!(a[4] == 1);
    prusti_assert!(a[5] == 1);
    prusti_assert!(a[6] == 1);
    prusti_assert!(a[7] == 1);
    prusti_assert!(a[8] == 1);
    prusti_assert!(a[9] == 1);
    prusti_assert!(a[10] == 1);
}

fn test11() {
    let mut a = [1; 100];
    a[1] = 2;
    prusti_assert!(a[1] == 2);
    prusti_assert!(a[0] == 1);
    prusti_assert!(a[2] == 1);
    prusti_assert!(a[3] == 1);
    prusti_assert!(a[4] == 1);
    prusti_assert!(a[5] == 1);
    prusti_assert!(a[0] == 2);     //~ ERROR: the asserted expression might not hold
}

//fn test10() {
    //let mut a = [1; 100];
    //let b = &mut a[1];
    //*b = 2;   FIXME
    //assert!(a[1] == 2);
    //assert!(a[0] == 1);
    //assert!(a[2] == 1);
    //assert!(a[3] == 1);
    //assert!(a[4] == 1);
    //assert!(a[5] == 1);
//}

//fn test11() {
    //let mut a = [1; 100];
    //let b = &mut a[1];
    //*b = 2;   FIXME
    //assert!(a[1] == 2);
    //assert!(a[0] == 1);
    //assert!(a[2] == 1);
    //assert!(a[3] == 1);
    //assert!(a[4] == 1);
    //assert!(a[5] == 1);
    //assert!(a[0] == 2);     the asserted expression might not hold
//}

fn main() {}
