//! Example: function `foo` that returns a permission on a reference contained in the argument

#![feature(nll)]

extern crate prusti_contracts;

struct IntPair { a: i32, b: (i32, i32) }

enum IntPairOption<'a> { Some(&'a mut IntPair), None }

fn foo<'a>(arg: IntPairOption<'a>) -> (i32, i32) {
    let mut x = IntPair { a: 111, b: (222, 333) };
    x.b.0 = 444;
    let y = x;
    let z = IntPairOption::Some(&mut y);
    y.b
}

fn main() {

}
