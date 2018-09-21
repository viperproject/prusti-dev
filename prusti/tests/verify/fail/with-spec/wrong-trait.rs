extern crate prusti_contracts;

struct S {
    f: i32
}

trait T {
    fn test(&mut self);
}

impl T for S {
    #[requires="true"]
    #[ensures="false"]
    fn test(&mut self) {} //~ ERROR
}

fn main() {}
