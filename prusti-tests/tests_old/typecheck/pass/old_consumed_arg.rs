//! Example: old expression on an argument that is consumed by the function

extern crate prusti_contracts;

struct IntBox {
    value: i32
}

#[ensures="result == old(my_box.value)"]
fn unbox(my_box: IntBox) -> i32 {
    my_box.value
}

fn main() {

}
