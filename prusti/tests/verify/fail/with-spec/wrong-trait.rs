
struct S {
    pub f: i32
}

impl From<i32> for S {
    #[requires="true"]
    #[ensures="false"]
    fn from(f: i32) -> S { //~ ERROR
        S { f }
    }
}

fn main() {}
