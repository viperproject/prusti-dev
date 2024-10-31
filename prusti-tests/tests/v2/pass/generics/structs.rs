use prusti_contracts::*;

#[pure]
#[ensures(true)]
fn foo<T>(a: T) -> bool { true }

struct X <T, U> {a: T, b: U}

#[trusted]
#[pure]
fn get_i8() -> i8 {0}

#[trusted]
#[pure]
fn get_i16() -> i16 {1}

#[requires(foo(X {a: get_i8(), b: get_i16()}))]
#[requires(foo(X {a: get_i16(), b: get_i8()}))]
#[requires(foo(get_i8()))]
fn main() {
}
