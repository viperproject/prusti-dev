use prusti_contracts::*;

fn main() {}

#[derive(Clone, Copy)]
pub struct A {
    inner: usize,
}

predicate! {
    pub fn a_invariant(a: &A) -> bool {
        a.inner > 10
    }
}

impl A {
    #[pure]
    #[ensures(a_invariant(self) ==> result > 10)]
    pub const fn foo(&self) -> usize {
        self.inner
    }
}

#[derive(Clone, Copy)]
pub struct B {
    a: A,
}

predicate! {
    pub fn b_invariant(b: &B) -> bool {
        a_invariant(&b.a)
    }
}

impl B {
    #[pure]
    #[requires(b_invariant(&self))]
    #[ensures(result > 10)]
    pub const fn inner(&self) -> usize {
        self.a.foo()
    }
    #[pure]
    #[requires(b_invariant(self))]
    pub const fn bar(&self) {
        assert!(self.inner() > 10);
    }
}
