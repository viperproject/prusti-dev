extern crate prusti_contracts;

macro_rules! my_assert {
    ( $( $args:expr ),* ) => {
        assert!( $( $args ),* ) //~ ERROR assert!(..) statement might not hold
    };
}

fn foo(x: bool) {
    my_assert!(x);
}

fn main() {

}
