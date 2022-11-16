use prusti_contracts::*;

fn main() {}


#[pure]
#[ensures(result == a.len())]
#[ensures(result == 17)]
fn array_foo(a: &[i32; 17]) -> usize {
    a.len()
}
