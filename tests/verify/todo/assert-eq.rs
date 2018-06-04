// error-pattern: error

extern crate prusti_contracts;

fn foo(x: i32, y: i32) {
    assert_eq!(x, y);
}

fn main() {

}
