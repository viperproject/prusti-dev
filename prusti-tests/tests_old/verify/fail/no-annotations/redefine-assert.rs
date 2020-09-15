use prusti_contracts::*;

macro_rules! assert {
    ( $( $args:expr ),* ) => {
        panic!( $( $args ),* ) //~ ERROR panic!(..) statement might panic
    };
}

fn foo(x: bool) {
    assert!(x);
}

fn main() {

}
