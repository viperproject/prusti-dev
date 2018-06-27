extern crate prusti_contracts;

macro_rules! my_assert {
    ( $( $args:expr ),* ) => {
        assert!( $( $args ),* )
    };
}

fn foo(x: bool) {
    my_assert!(x);  //~ ERROR assert!(..) statement might not hold
}

fn main() {

}
