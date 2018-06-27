extern crate prusti_contracts;

macro_rules! assert {
    ( $( $args:expr ),* ) => {
        panic!( $( $args ),* )
    };
}

fn foo(x: bool) {
    assert!(x);  //~ ERROR panic!(..) statement might panic
}

fn main() {

}
