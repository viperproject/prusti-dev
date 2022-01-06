use prusti_contracts::*;

#[pure]
fn fun(i: i32) -> bool { i > 0 }

// It is exceptionally hard to find an example
// where a Viper `exists` succeeds but a `forall` fails.
// This seems to do the trick though.
#[requires(fun(_k))]
#[ensures(exists(|k:i32| fun(k)))]
fn test(_k: i32) { }

fn main() { test(1) }
