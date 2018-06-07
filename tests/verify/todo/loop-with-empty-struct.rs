//! Example: program with a loop and a structure with no fields

#![feature(nll)]

extern crate prusti_contracts;

struct S {}

enum OptionRefS<'a> {
    None,
    Some(&'a mut S)
}

fn random() -> bool {
    true
}

fn consume(a: OptionRefS) {}

fn foo<'a>(mut x: S) {
    let mut a: OptionRefS;
    let mut b: OptionRefS;
    if random() {
        a = OptionRefS::Some(&mut x);
        b = OptionRefS::None;
    } else {
        a = OptionRefS::None;
        b = OptionRefS::Some(&mut x);
    }
    while random() {
        // inv: Option<S>(a) && Option<S>(b)
        let tmp = a;
        a = b;
        b = tmp;
    }
    consume(a);
    consume(b);
}

fn main() {}
