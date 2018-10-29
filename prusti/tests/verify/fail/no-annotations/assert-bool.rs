extern crate prusti_contracts;

fn foo(x: bool) {
    assert!(x);  //~ ERROR assert!(..) statement might not hold
}

fn main() {

}
