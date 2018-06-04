// error-pattern: error[P0002]

extern crate prusti_contracts;

macro_rules! my_assert {
    ( $( $args:expr ),* ) => {
        panic!( $( $args ),* )
    };
}

fn foo(x: bool) {
    my_assert!(x);
}

fn main() {

}
