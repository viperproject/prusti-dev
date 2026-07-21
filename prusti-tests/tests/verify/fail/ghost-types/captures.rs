// Ghost bodies must comply with `Fn` capture rules, enforced by the
// never-called checker closure the `ghost!` macro emits alongside the inline
// body: outer variables cannot be mutated, mutably borrowed (including writes
// through references in scope), or consumed. Each violation errors twice:
// once in the checker closure, once as the inline copy conflicting with the
// closure's capture.

use prusti_contracts::*;

fn mutate_outer() {
    let mut x = Ghost::new(5u32);
    ghost! {
        x = Ghost::new(10); //~ERROR: cannot assign to value, as it is a captured variable in a `Fn` closure
        //~| ERROR: cannot assign to `x` because it is borrowed
    };
}

fn mutably_borrow_outer() {
    let mut x = 5u32;
    ghost! {
        let _r = &mut x; //~ERROR: cannot borrow value as mutable, as it is a captured variable in a `Fn` closure
        //~| ERROR: cannot borrow `x` as mutable more than once at a time
    };
}

fn write_through_reference(r: &mut i64) {
    ghost! {
        *r = 5; //~ERROR: cannot assign to value, as it is a captured variable in a `Fn` closure
        //~| ERROR: cannot assign to `*r` because it is borrowed
    };
}

struct NotCopy(i64);

fn consume(_: NotCopy) {}

fn move_outer() {
    let v = NotCopy(1);
    ghost! {
        consume(v); //~ERROR: cannot move out of value, a captured variable in an `Fn` closure
        //~| ERROR: use of moved value: `v`
    };
}

fn main() {}
