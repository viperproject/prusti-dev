extern crate prusti_contracts;
use prusti_contracts::*;

struct Struct {
  field: u32
}

#[pure]
fn inner(m: &Struct) -> &u32 {
    &m.field
}

#[pure]
fn outer(field: &u32) -> bool {
    true
}

#[pure]
fn pred(m: &Struct) -> bool {
    outer(inner(&m)) //~ ERROR There is no procedure contract for loan bw6. This could happen if you are chaining pure functions, which is not fully supported.
}

fn main(){}
