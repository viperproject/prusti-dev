extern crate prusti_contracts;

fn main() {
    let y = 0;
    let _z = 1 / y;  //~ ERROR assertion might fail with "attempt to divide by zero"
}
