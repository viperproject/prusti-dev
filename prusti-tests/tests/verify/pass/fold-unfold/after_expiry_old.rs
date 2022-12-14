use prusti_contracts::*;

struct Inner(i32);

struct Outer {
  value: Inner,
}

#[pure]
#[trusted]
fn condition(v: &Outer) -> bool {
  unimplemented!()
}

#[trusted]
#[ensures(*result === *old(&v.value))]
#[after_expiry(old(condition(&v)))]
fn deref_mut(v: &mut Outer) -> &mut Inner {
  &mut v.value
}

fn test(g: &mut Outer) {
  deref_mut(g);
}

#[trusted]
fn main () {}
