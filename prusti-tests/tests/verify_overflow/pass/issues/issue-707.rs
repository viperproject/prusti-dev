use prusti_contracts::*;

#[derive(Clone,Copy)]
pub struct A {
    _inner: usize,
}

#[derive(Clone,Copy)]
pub struct B {
    inner: A,
}

impl B {
    #[pure] // <-- removing this attribute makes the below error go away
    // #[trusted] // <-- adding this attribute doesn't help
    pub fn get(&self) -> A {
        self.inner
    }
}

// This method triggers the Prusti error:
// "error: [Prusti internal error] consistency error in test: Consistency error:
// expected the same type, but got Ref and Snap$m_A$_beg_$_end_ (@0.0)"
// The error only shows up when returning an ADT, there is no error when
// the return type is a primitive.
pub fn test(b: &B) -> A {
    b.get()
}

fn main() {}
