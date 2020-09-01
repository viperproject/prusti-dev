#![feature(never_type)]

extern crate prusti_contracts;

fn diverging() -> ! {
    diverging()
}

fn test() {
    diverging();
    // The return type is `Never`, so Prusti should assume `false` here.
    // The following assertion should not raise verification errors
    assert!(1 == 2);
}

fn main() {}
