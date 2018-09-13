//! Example: test specification of box dereferentiation

extern crate prusti_contracts;

#[ensures="result == old(*my_box)"]
fn foo(my_box: Box<i32>) -> i32 {
    *my_box
}

fn main() {

}
