#![feature(nll)]

extern crate prusti_contracts;

#[derive(Clone)]
struct IntPair { a: i32, b: (i32, i32) }

enum IntPairOption<'a> { Some(&'a mut IntPair), None }

fn foo() -> i32 {
    let mut x = IntPair { a: 11, b: (22, 33) };
    let mut k= IntPair { a: 44, b: (55, 66) };
    let mut arg = IntPairOption::Some(&mut k);
    x.b.0 = 77;
    let mut y = x;
    let z = IntPairOption::Some(&mut y);
    match arg {
        IntPairOption::Some(k) => k.a,
        IntPairOption::None => 88
    }
}

fn main() {

}
