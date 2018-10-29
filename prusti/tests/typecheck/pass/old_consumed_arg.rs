//! Example: old expression on an argument that is consumed by the function

struct IntBox {
    value: i32
}

#[ensures="result == old(my_box.value)"]
fn unbox(my_box: IntBox) -> i32 {
    my_box.value
}

fn main() {

}
