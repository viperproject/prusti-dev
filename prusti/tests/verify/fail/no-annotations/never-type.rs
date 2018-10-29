#![feature(never_type)]

fn diverging() -> ! {
    panic!();  //~ ERROR panic!(..) statement might panic
}

fn main() {
}
