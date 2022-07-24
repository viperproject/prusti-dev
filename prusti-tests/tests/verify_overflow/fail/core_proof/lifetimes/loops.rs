// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main(){}

#[trusted]
struct WrapperIterator<'a, T>{
    iter_mut: std::slice::IterMut<'a, T>,
}
impl<'a, T> WrapperIterator<'a, T> {
    #[trusted]
    fn new(x: &'a mut Vec<T>) -> Self {
        WrapperIterator {
            iter_mut: x.iter_mut(),
        }
    }
}
impl<'a, T> Iterator for WrapperIterator<'a, T> {
    type Item = &'a mut T;
    #[trusted]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next()
    }
}
fn test1() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    for x in &mut v {}
}
fn test1_assert_false() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    for x in &mut v {}
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn test2() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    let mut n = 4;
    let mut s = &mut n;
    assert!(*s == 4);
    for x in &mut v {
        s = x;
    }
    *s = 4;
    assert!(*s == 4);
}
fn test2_assert_false() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    let mut n = 4;
    let mut s = &mut n;
    assert!(*s == 4);
    for x in &mut v {
        s = x;
    }
    assert!(*s == 4);      //~ ERROR: the asserted expression might not hold
    *s = 4;
}

struct X {
    x: i32,
}
fn test3() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<X> = WrapperIterator::new(&mut ve);
    for x in &mut v {}
}
fn test3_assert_false() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<X> = WrapperIterator::new(&mut ve);
    for x in &mut v {}
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
