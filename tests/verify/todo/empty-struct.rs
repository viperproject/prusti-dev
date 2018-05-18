#![feature(nll)]

extern crate prusti_contracts;

struct S {}

fn random() -> bool {
    true
}

fn use_ab(a: Option<&mut S>, b: Option<&mut S>) {}

fn foo<'a>(mut x: S, y: &'a mut S) {
    let mut a: Option<&mut S>;
    let mut b: Option<&mut S>;
    if random() {
        a = Some(&mut x);
        b = None;
    } else {
        a = None;
        b = Some(&mut x);
    }
    while random() {
        // inv: Option<S>(a) && Option<S>(b)
        let tmp = a;
        a = b;
        b = tmp;
    }
    // in order to preserve permissions: use a magic wand
    use_ab(a, b);
}

fn main() {}
