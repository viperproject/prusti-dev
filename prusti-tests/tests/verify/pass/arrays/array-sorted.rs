use prusti_contracts::*;

fn main() {}

// FIXME: predicate here
#[pure]
fn sorted_ish(a: &[i32; 4]) -> bool {
    a[0] <= a[1]
        && a[1] <= a[2]
        && a[2] <= a[3]
}

fn do_it() {
    let a = [0, 1, 2, 3];

    assert!(sorted_ish(&a));
}
