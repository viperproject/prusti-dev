use prusti_contracts::*;

struct S {
    pub f: i32
}

impl S {
    #[requires(f == 123)]
    #[ensures(result.f == 123)]
    fn from(f: i32) -> S {
        S { f }
    }
}

fn main() {}
