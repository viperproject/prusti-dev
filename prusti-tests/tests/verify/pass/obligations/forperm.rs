use prusti_contracts::*;

obligation! {
    fn obl(amount: usize, x: usize);
}

// this was causing the method purifier optimization to
// crash due to mishandling of the quantified
// variables in forperm expressions

#[trusted]
#[requires(obl(1, 1))]
fn consume() {}

#[requires(obl(1, 1))]
#[ensures(result == 44)]
fn f() -> usize {
    consume();
    44
}

fn main() {}
