// compile-flags: -Penable_purification_optimization=true

use prusti_contracts::*;

fn test1() {
    let mut i = 0;
    while i < 5 {
        i += 1;     //~ ERROR: attempt to add with overflow
    }
    let mut j = 0;
    assert!(i == j);
}

fn test2() {
    let mut i = 0;
    while i < 5 {
        assert!(i < 5);  //~ ERROR: the asserted expression might not hold
        i += 1;
    }
    let mut j = 0;
    assert!(i == j);
}

fn test3() {
    let mut i = 0;
    while i < 5 {
        body_invariant!(i < 5);
        i += 1;
    }
    let mut j = 0;
    assert!(i == j);    //~ ERROR: the asserted expression might not hold
}

fn test4(v: &mut[i32]) {
    let mut zero_num_start = 0;
    let mut i = 0;
    while i < v.len() {
        assert!(i < v.len()); //~ ERROR: the asserted expression might not hold
        i += 1;
    }
}

fn test5(v: &mut[i32]) {
    let mut zero_num_start = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i] == 0 {  //~ ERROR: the array or slice index may be out of bounds
            zero_num_start += 1;
        }
        i += 1;
    }
}

fn test6(v: &mut[i32]) {
    let mut zero_num_start = 0;
    let mut i = 0;
    while i < v.len() {
        body_invariant!(i < v.len());
        if v[i] == 0 {
            zero_num_start += 1;
        }
        i += 1;
    }
    let mut zero_num_end = 0;
    let mut i = 0;
    while i < v.len() {
        body_invariant!(i < v.len());
        if v[i] == 0 {
            zero_num_end += 1;
        }
        i += 1;
    }
    assert!(zero_num_start == zero_num_end);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
