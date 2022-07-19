// compile-flags: -Penable_ghost_constraints=true
use prusti_contracts::*;

trait A<T, U> {
    type AssocType;
}

trait SomeTrait<X, Y> {
    type AssocType;
    fn foo(&self) -> i32;
}

struct FooMatch;
impl A<i8, i16> for FooMatch {
    type AssocType = i32;
}
impl SomeTrait<i8, i16> for FooMatch {
    type AssocType = i32;
    fn foo(&self) -> i32 { 42 }
}

struct FooNoMatch1;
impl A<i8, i16> for FooNoMatch1 {
    type AssocType = i32;
}
impl SomeTrait<i8, i8> for FooNoMatch1 {
    type AssocType = i32;
    fn foo(&self) -> i32 { 42 }
}

struct FooNoMatch2;
impl A<i8, i16> for FooNoMatch2 {
    type AssocType = i32;
}
impl SomeTrait<i8, i16> for FooNoMatch2 {
    type AssocType = i16;
    fn foo(&self) -> i32 { 42 }
}

#[extern_spec]
trait SomeTrait<#[generic] X, #[generic] Y> {
    #[ghost_constraint(Self: A<X, Y, AssocType = <Self as SomeTrait<X, Y>>::AssocType> , [
    ensures(result > 0)
    ])]
    fn foo(&self) -> i32;
}

fn verify_match() {
    let f = FooMatch;
    assert!(f.foo() > 0);
}

fn verify_no_match_1() {
    let f = FooNoMatch1;
    assert!(f.foo() > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}

fn verify_no_match_2() {
    let f = FooNoMatch2;
    assert!(f.foo() > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}

fn main() {
}