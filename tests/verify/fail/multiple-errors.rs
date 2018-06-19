// error-pattern: error[P0003]
// error-pattern: error[P0003]
// error-pattern: error[P0003]

extern crate prusti_contracts;

fn foo() {
    assert!(false);
}

fn bar() {
    assert!(false);
}

fn main() {
    assert!(false);
}
