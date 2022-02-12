// ignore-test
// FIXME: this test passes for the original encoder, but it fails on a todo!() in the new vir high encoder
// FIXME: see https://github.com/viperproject/prusti-dev/issues/812

use prusti_contracts::*;

fn main() {}

#[pure]
#[requires(forall(|i: usize| (0 <= i && i < slice.len()) ==> (slice[i] > 10), triggers=[(slice[i],slice.len(),baz(slice))]))]
fn foo(slice: &[i32]) {}

#[requires(forall(|i: usize| (0 <= i && i < array.len()) ==> (array[i] > 10), triggers=[(array[i],array.len(),baz(array),)]))]
fn bar(array: &[i32; 10]) {}

#[pure]
#[trusted]
fn baz(slice: &[i32]) {}
