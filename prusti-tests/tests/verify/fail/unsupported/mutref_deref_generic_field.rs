use prusti_contracts::*;
use std::marker::PhantomData;

// A struct is encoded once over its generic parameters, so a field of generic
// type only has the shallow snapshot of its instantiation, even in the deep
// snapshot of the struct: the value behind a mutable reference in it is not
// known in pure code.
pub struct W<'a, T> {
    pub t: T,
    pub p: PhantomData<&'a ()>,
}

trait Tr {
    #[ensures(result == old(*w.t))] //~ ERROR: dereference of the mutable reference `&mut i32` in pure code
    fn get<'a>(&self, w: W<'a, &'a mut i32>) -> i32;
}

struct S;

impl Tr for S {
    fn get<'a>(&self, w: W<'a, &'a mut i32>) -> i32 {
        *w.t
    }
}

// The two calls see different values behind the reference.
fn client<X: Tr>(t: &X, x: &mut i32) {
    *x = 1;
    let r1 = t.get(W { t: &mut *x, p: PhantomData });
    *x = 2;
    let r2 = t.get(W { t: &mut *x, p: PhantomData });
    prusti_assert!(r1 == r2); //~ ERROR: assertion might not hold
}

fn main() {}
