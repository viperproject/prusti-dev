extern crate prusti_contracts;

fn foo() {
    assert!(false);  //~ ERROR assert!(..) statement might not hold
}

fn bar() {
    assert!(false);  //~ ERROR assert!(..) statement might not hold
}

fn main() {
    assert!(false);  //~ ERROR assert!(..) statement might not hold
}
