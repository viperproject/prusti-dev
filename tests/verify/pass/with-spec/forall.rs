extern crate prusti_contracts;

#[requires="true ==> forall x: i32, y45: usize :: x > 0 ==> y45 + 2 >= 2"]
fn main() {
    let y = 1 + 2;
}
