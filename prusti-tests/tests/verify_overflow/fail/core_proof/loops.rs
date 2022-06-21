// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

fn test1() {
    let mut i = 0;
    while i != 5 {
        body_invariant!(i < 5);
        i += 1;
    }
    assert!(i == 5);
}

fn test2() {
    let mut i = 0;
    while i < 5 {
        body_invariant!(i < 5);
        i += 1;
        if !(i < 5) {
            assert!(i == 5);
        }
    }
    assert!(i == 5);
}

fn test3() {
    let mut i = 0;
    while i < 5 {
        body_invariant!(i < 5);
        i += 1;
    }
    assert!(false);    //~ ERROR: the asserted expression might not hold
}

fn test4() {
    let mut i = 0;
    while i < 5 {
        assert!(i < 5);
        i += 1;
        assert!(i <= 5);
    }
    assert!(!(i < 5));
}

fn test5() {
    let mut i = 0;
    while i < 5 {
        assert!(i < 5);
        i += 1;
        assert!(i <= 5);
    }
    assert!(i == 5);    //~ ERROR: the asserted expression might not hold
}

fn test6() {
    let mut i = 0;
    while i < 5 {
        assert!(i < 5);
        i += 1;
        assert!(i <= 5);
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }
}

fn next() -> Option<u32> {
    None
}

fn test7() {
    while let Some(n) = next() { }
}

fn test8() {
    while let Some(n) = next() { }
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

#[ensures(old(a) == old(a))]
fn next2(a: u32) -> Option<u32> {
    None
}

fn test9() {
    while let Some(n) = next2(3) {
        body_invariant!(true);
    }
}

fn test10() {
    while let Some(n) = next2(3) {
        body_invariant!(true);
    }
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct T;

impl T {
    fn check(self) -> bool {
        true
    }
}

struct E;

fn next3() -> Result<Option<T>, E> {
    Ok(None)
}

fn test11() -> Result<T, E> {
    while let Some(n) = next3()? { }
    Err(E)
}

fn test12() -> Result<T, E> {
    while let Some(n) = next3()? {
        body_invariant!(true);
    }
    Err(E)
}

fn test13() -> Result<T, E> {
    while let Some(n) = next3()? {
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }
    Err(E)
}

fn test14() -> Result<T, E> {
    while let Some(n) = next3()? { }
    assert!(false);     //~ ERROR: the asserted expression might not hold
    Err(E)
}

fn test15() -> Result<T, E> {
    while let Some(n) = next3()? {
        body_invariant!(true);
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }
    Err(E)
}

fn test16() -> Result<T, E> {
    while let Some(n) = next3()? {
        body_invariant!(true);
    }
    assert!(false);     //~ ERROR: the asserted expression might not hold
    Err(E)
}

fn test17() -> Result<T, E> {
    while let Some(n) = next3()? {
        if n.check() {
            break;
        }
    }
    Err(E)
}

fn test18() -> Result<T, E> {
    while let Some(n) = next3()? {
        if n.check() {
            break;
        } else {
            continue;
        }
    }
    Err(E)
}

fn next4() -> u32 {
    4
}

fn test19() -> u32 {
    let result = loop {
        let result = next4();
        if result > 4 {
            break result;
        }
    };
    result
}

fn test20() -> u32 {
    let result = loop {
        let result = next4();
        if result > 4 {
            break result;
        }
        body_invariant!(true);
    };
    result
}

fn test21() -> u32 {
    let result = loop {
        body_invariant!(true);
        let result = next4();
        if result > 4 {
            break result;
        }
    };
    result
}

fn test22() -> u32 {
    let result = loop {
        let result = next4();
        if result > 4 {
            break result;
        }
    };
    assert!(false); //~ ERROR: the asserted expression might not hold
    result
}

fn test23() {
    loop {}
}

fn main() {}

