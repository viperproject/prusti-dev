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
    for x in &mut v {
        *x = 4;
    }
    // for x in &mut v {
    //     assert!(*x == 4);
    // }
}
fn test1_assert_false() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    for x in &mut v {
        // *x = 4;
    }
    assert!(false) //~ ERROR
}
