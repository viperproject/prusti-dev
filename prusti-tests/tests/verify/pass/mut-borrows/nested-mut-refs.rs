// Nested mutable references: the indirect predicates of every nested
// lifetime projection (e.g. `x|'b` for `x: &'a mut &'b mut i32`) must be
// part of the function contract.
use prusti_contracts::*;

#[requires(**x >= 0)]
#[ensures(**x == 5)]
fn write_inner<'a, 'b>(x: &'a mut &'b mut i32) {
    **x = 5;
}

#[requires(**x > 0)]
fn chained<'a, 'b>(x: &'a mut &'b mut i32) {
    write_inner(x);
    write_inner(x);
    **x = 7;
    assert!(**x == 7);
}

fn triple<'a, 'b, 'c>(x: &'a mut &'b mut &'c mut i32) {
    ***x = 9;
}

struct Holder<'b> {
    r: &'b mut i32,
}

fn through_struct<'a, 'b>(h: &'a mut Holder<'b>) {
    *h.r = 3;
}
