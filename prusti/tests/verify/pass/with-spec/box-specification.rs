//! Example: test specification of box dereferentiation

#[ensures="result == old(*my_box)"]
fn foo(my_box: Box<i32>) -> i32 {
    *my_box
}

fn main() {

}
