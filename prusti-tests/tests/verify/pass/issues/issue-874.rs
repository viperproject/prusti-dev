use prusti_contracts::*;

#[requires(match x {
    Some(v) => *v > 0,
    None => true,
})]
fn foo(x: &mut Option<i32>) {}

fn main() { }
