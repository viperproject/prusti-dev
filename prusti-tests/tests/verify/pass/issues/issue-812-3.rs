use prusti_contracts::*;

fn main() {}

#[requires(forall(|i: usize| (0 <= i && i < slice.len()) ==> (bar(slice[i])), triggers=[(bar(slice[i]),(slice.len()),)]))]
fn foo(slice: &[i32]) {}

#[pure]
#[trusted]
fn bar(a: i32) -> bool { true }

#[requires(slice.len() == 1)]
fn baz(slice: &[i32]) {
    if bar(slice[0]) {
        foo(slice);
    }
}
