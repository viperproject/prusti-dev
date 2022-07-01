use prusti_contracts::*;

fn main() {}

#[pure]
fn foo<T>(x: &T) -> bool { true }

#[ensures(foo(&x))]
fn bar<T>(x: T) {
    drop(x);
}

fn drop<T>(x: T) {}

#[ensures(foo(&x))]
fn baz<T>(x: T, v: i32) {
    if v > 0 { baz(x, v-1) }
}
