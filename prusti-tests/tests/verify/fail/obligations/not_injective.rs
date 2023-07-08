use prusti_contracts::*;

obligation! {
    fn obl(amount: usize);
}

#[requires(forall(|x: usize| obl(1)))]
fn f1() {} //~ ERROR quantified resource in the function's precondition might not be injective

#[ensures(forall(|x: usize| obl(1)))]
fn f2() {} //~ ERROR quantified resource in the function's postcondition might not be injective

#[trusted]
#[requires(forall(|x: usize| obl(1)))]
fn a3() {}

fn f3() {
    a3(); //~ ERROR quantified resource in the callee's precondition might not be injective
}

#[trusted]
#[ensures(forall(|x: usize| obl(1)))]
fn a4() {}

fn f4() {
    a4(); //~ ERROR quantified resource in the callee's postcondition might not be injective
}

fn f5() {
    prusti_assert!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the asserted expression might not be injective
}

fn f6() {
    loop {
        body_invariant!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the loop invariant might not be injective
    }
}

// TODO add cases for assume, inhale, exhale

fn main() {}
