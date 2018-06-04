// error-pattern: error[P0005]

extern crate prusti_contracts;

fn main() {
    let y = 0;
    let _z = 1 / y;
}
