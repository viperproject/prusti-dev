use prusti_contracts::*;

#[ensures((x == 5 || x == 7) == (result == 1))]
fn a(x: u64) -> u64 {
    if x == 5 || x == 7 { 1 } else { 0 }
}

#[ensures(x == 5 || x == 7 <==> result == 1)]
fn b(x: u64) -> u64 {
    if x == 5 || x == 7 { 1 } else { 0 }
}

#[ensures(result == 1 <== x == 0)]
fn c(x: u64) -> u64 {
    if x == 0 { 1 } else { 0 }
}

fn main() {}
