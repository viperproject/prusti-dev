use prusti_contracts::*;

obligation! {
    fn obl(amount: usize);
}

// note that these expressions are illegal and are only meant to pass the Rust type check
#[ensures(obl(33))]
#[ensures(obl(3 + 3) & obl(8 - 1))]
#[ensures(obl(0) || obl(78))]
#[ensures(obl(7) ==> obl(42))]
fn main() {}
