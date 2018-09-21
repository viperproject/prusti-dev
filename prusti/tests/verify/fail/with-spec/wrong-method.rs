extern crate prusti_contracts;

struct S {
    f: i32
}

impl S {
    #[requires="true"]
    #[ensures="false"]
    pub fn test(self) {} //~ ERROR
}

fn main() {}
