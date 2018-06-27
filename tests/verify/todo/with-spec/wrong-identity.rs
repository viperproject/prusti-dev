extern crate prusti_contracts;

#[ensures="result == old(x)"] //~ ERROR
fn identity(x: i32) -> i32 {
    x + 1
}

fn main() {

}
