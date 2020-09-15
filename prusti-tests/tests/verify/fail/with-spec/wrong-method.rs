use prusti_contracts::*;

struct S {
    f: i32
}

impl S {
    #[requires(true)]
    #[ensures(false)] //~ ERROR postcondition
    pub fn test(self) {}
}

fn main() {}
