#![allow(dead_code)]

use prusti_contracts::*;

#[predicate]
fn pred_id(x: bool) -> bool {
    x
}

fn illegal_use() {
    let _x = pred_id(true);
}

fn illegal_ref(_pred: fn(bool) -> bool) {}

struct Outer;

impl Outer {
    pub fn nested() {
        struct Inner;

        impl Inner {
            #[predicate]
            fn inner_pred(b: bool) -> bool {
                b
            }

            fn illegal() {
                illegal_ref(Self::inner_pred)
            }
        }
    }
}

fn main() {
    illegal_use();
    illegal_ref(pred_id);
}
