// error-pattern: error[P0002]

extern crate prusti_contracts;

macro_rules! assert {
    ( $( $args:expr ),* ) => {
        panic!( $( $args ),* )
    };
}

fn foo(x: bool) {
    assert!(x);
}

fn main() {

}
