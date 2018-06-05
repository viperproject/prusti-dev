#![feature(nll)]

extern crate prusti_contracts;

struct T {
    v: i32
}

struct S {
    f: T,
    g: T
}

fn random() -> bool {
    true
}

fn consume_s(x: S) {}

fn consume_t(x: T) {}

fn main() {
    let mut x = S {
        f: T { v: 11 },
        g: T { v: 22 },
    };

    let t = if random() {
        // move out x.f
        consume_t(x.f);
    } else {
        // move out x.g
        consume_t(x.g);
    };

    // here there is no full permission on x

    x.f = T { v: 33 };
    x.g = T { v: 44 };

    // here we can have a full permission on x

    consume_s(x);
}
