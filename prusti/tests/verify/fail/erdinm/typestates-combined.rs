extern crate prusti_contracts;

use std::marker::PhantomData;

trait IntState {}

struct Even; impl IntState for Even {}
struct Odd;  impl IntState for Odd {}

#[invariant="S == Even ~~> self.i % 2 == 0"]
#[invariant="S == Odd  ~~> self.i % 2 != 0"]
struct Int<S: IntState> {
    i: i32,
    s: PhantomData<S>,
}

impl<Z: IntState> Int<Z> {
    #[requires="Z == Even ~~> i % 2 == 0"]
    #[requires="Z == Odd  ~~> i % 2 != 0"]
    fn new(i: i32) -> Int<Z> {
        Int {
            i,
            s: PhantomData,
        }
    }

    //#[requires="Z == Even ~~> i % 2 == 0"]
    //#[requires="Z == Odd  ~~> i % 2 != 0"]
    fn new_fail(i: i32) -> Int<Z> { //~ ERROR type invariants
        Int {
            i,
            s: PhantomData,
        }
    }

    fn test_incr2(&mut self) {
        self.i += 2;
    }

    fn test_incr3(&mut self) { //~ ERROR type invariants
        self.i += 3;
    }

    fn test_plus2(self) -> Self {
        Int {
            i: self.i + 2,
            s: PhantomData,
        }
    }

    fn test_plus3(self) -> Self { //~ ERROR type invariants
        Int {
            i: self.i + 3,
            s: PhantomData,
        }
    }

    fn test_double(self) -> Int<Even> {
        Int::new(self.i * 2)
    }

    fn test_triple(self) -> Int<Even> {
        Int::new(self.i * 3) //~ ERROR precondition might not hold
    }
}

fn test1(int: &mut Int<Even>) {
    assert!(int.i % 2 == 0);
}

fn test1_fail<S: IntState>(int: &mut Int<S>) {
    assert!(int.i % 2 == 0); //~ ERROR assert!(..) statement might not hold
}

fn test2(int: &mut Int<Odd>) {
    assert!(int.i % 2 != 0);
}

fn test2_fail<S: IntState>(int: &mut Int<S>) {
    assert!(int.i % 2 != 0); //~ ERROR assert!(..) statement might not hold
}

#[requires="i % 2 == 0"] // even
fn test3(i: i32) -> Int<Even> {
    Int::new(i)
}

#[requires="i % 2 == 0"] // even
fn test3_fail(i: i32) -> Int<Odd> { // wrong return type state
    Int::new(i) //~ ERROR precondition might not hold
}

#[requires="i % 2 != 0"] // odd
fn test4(i: i32) -> Int<Odd> {
    Int::new(i)
}

#[requires="i % 2 != 0"] // odd
fn test4_fail(i: i32) -> Int<Even> {
    Int::new(i) //~ ERROR precondition might not hold
}

fn main() {}
