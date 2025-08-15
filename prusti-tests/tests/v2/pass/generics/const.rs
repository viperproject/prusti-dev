use prusti_contracts::*;

#[requires(N > 5)]
#[ensures(N > 3)]
fn foo<const N: u32>() -> u32 {
    if N < 4 {
        unreachable!();
    }
    N - 2
}

#[requires(N > 5)]
fn passthrough<const N: u32>() -> u32 {
    foo::<N>()
}

fn main() {
    foo::<6>();
}
