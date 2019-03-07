extern crate prusti_contracts;

struct S {
    pub f: i32
}

impl From<i32> for S {
    #[requires="true"]
    #[ensures="false"] //~ ERROR
    fn from(f: i32) -> S {
        S { f }
    }
}

fn main() {}
