#![feature(nll)]

// error-pattern: error[P0003]

extern crate prusti_contracts;

enum IntOption {
    Some(i32),
    None
}

fn foo(x: IntOption) -> i32 {
    let y = IntOption::Some(123);
    let ret = match x {
        IntOption::Some(y) => y,
        IntOption::None => 456
    };
    assert!(false);
    ret
}

fn main() {

}
