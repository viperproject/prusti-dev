extern crate prusti_contracts;

#[ensures="result == old(x)"] //~ ERROR postcondition might not hold
fn identity(x: i32) -> i32 {
    x + 1
}

fn main() {

}
