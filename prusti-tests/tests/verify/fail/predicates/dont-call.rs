use prusti_contracts::*;


#[predicate]
fn pred_id(x: bool) -> bool {
    x
}

fn illegal_use() {
    let _x = pred_id(true);  //~ ERROR call to predicate from non-specification code is not allowed
}


fn main() {
    illegal_use();
}
