use prusti_contracts::*;

#[predicate]
fn pred_id(x: bool) -> bool {
    x
}

fn illegal_use() {
    let _x = pred_id(true);
}

fn illegal_ref(_pred: fn(bool) -> bool) {}

fn main() {
    illegal_use();
    illegal_ref(pred_id);
}
