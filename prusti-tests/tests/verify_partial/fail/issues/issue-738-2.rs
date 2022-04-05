use prusti_contracts::*;

fn main() {}

#[pure]
pub fn get(a: &usize) -> usize {
    *a //~^ ERROR
}
fn foo(a: &usize) {
    let v = get(a);
}
