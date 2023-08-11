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
    loop {
        body_invariant!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the loop invariant might not be injective
    }
}

fn f6() {
    prusti_assert!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the asserted expression might not be injective
}

fn f7() {
    // Viper currently doesn't seem to report non-injective QP in `assume`
    prusti_assume!(forall(|x: usize| obl(1)));
}

fn f8() {
    prusti_exhale!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the exhaled expression might not be injective
}

fn f9() {
    prusti_inhale!(forall(|x: usize| obl(1))); //~ ERROR quantified resource in the inhaled expression might not be injective
}

fn f10() {
    // Viper currently doesn't seem to report non-injective QP in `refute`
    prusti_refute!(forall(|x: usize| obl(1)));
}

fn main() {}
