#![feature(never_type)]

fn diverging() -> ! {
    panic!();  //~ ERROR panic!(..) statement might be reachable
}

fn main() {}
