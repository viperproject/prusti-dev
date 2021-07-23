use prusti_contracts::*;

trait Foo {
    #[ensures(result > 42)]
    fn foo(&self) -> i32;
}

struct Dummy {
    inner: i32,
}

#[refine_trait_spec]
impl Foo for Dummy {
    #[ensures(result > 84)]
    fn foo(&self) -> i32 {
        if self.inner > 84 {
            self.inner
        } else {
            102
        }
    }
}

fn main() {
    let d = Dummy { inner: 144 };
    let val = d.foo();
    assert!(val > 84);
}

