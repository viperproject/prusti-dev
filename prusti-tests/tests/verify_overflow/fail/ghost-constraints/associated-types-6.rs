// compile-flags: -Penable_ghost_constraints=true
use prusti_contracts::*;

trait A<T, U> {
    type AssocType;
}

struct FooMatch;
impl A<i8, i16> for FooMatch {
    type AssocType = i32;
}

struct FooNoMatch1;
impl A<i16, i8> for FooNoMatch1 {
    type AssocType = i32;
}

struct FooNoMatch2;
impl A<i8, i16> for FooNoMatch2 {
    type AssocType = i16;
}


#[trusted]
#[ghost_constraint(T: A<i8, i16, AssocType = i32> , [
    ensures(result > 0)
])]
fn foo<T>(x: T) -> i32 {
    42
}

fn verify_match() {
    let f = FooMatch;
    assert!(foo(f) > 0);
}

fn verify_no_match_1() {
    let f = FooNoMatch1;
    assert!(foo(f) > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}

fn verify_no_match_2() {
    let f = FooNoMatch2;
    assert!(foo(f) > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}

fn main() {
}