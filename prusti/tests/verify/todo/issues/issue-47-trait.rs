
struct S {
    f: i32
}

trait T {
    fn test(&mut self);
}

impl T for S {
    #[requires="self.f == 123"]
    #[ensures="self.f == 123"]
    fn test(&mut self) {
        let x = 123;
        assert!(self.f == x);
    }
}

fn main() {}
