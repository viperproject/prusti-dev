// FIXME: remove this compile flag when the new encoder is finished
// compile-flags: -Puse_new_encoder=false
use prusti_contracts::*;

fn main() {}

#[derive(Copy, Clone)]
pub struct A {
    inner: usize,
}

impl A {
    #[pure]
    pub const fn get(&self) -> usize {
        self.inner
    }
}

pub struct B {
    a: A,
}

impl B {
    #[pure]
    #[trusted]
    pub fn foo(&self, a: usize, b: usize) -> &[u8] {
        unimplemented!()
    }

    #[pure]
    #[ensures(result == self.foo(a.get(), b))]
    pub fn bar(&self, a: A, b: usize) -> &[u8] {
        self.foo(a.get(), b)
    }

    #[pure]
    pub fn baz(&self) -> &[u8] {
        self.bar(self.a, 1)
    }
}
