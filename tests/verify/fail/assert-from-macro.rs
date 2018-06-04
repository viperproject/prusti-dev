// error-pattern: error[P0003]

extern crate prusti_contracts;

macro_rules! my_assert {
    ( $( $args:expr ),* ) => {
        assert!( $( $args ),* )
    };
}

fn foo(x: bool) {
    my_assert!(x);
}

fn main() {

}
