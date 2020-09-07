extern crate prusti_contracts;

unsafe trait Foo {
    #[ensures="result > 42"]
    fn foo(&self) -> i32;
}

struct Dummy {
    inner: i32,
}

unsafe impl Foo for Dummy {
    #[ensures="result > 84"]
    fn foo(&self) -> i32 {
        if self.inner > 84 {
            self.inner
        } else {
            102
        }
    }
}

fn main() {}

