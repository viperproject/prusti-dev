use std::cell::*;

#[analyzer::run]
pub fn break_it(rc: &RefCell<i32>, r: Ref<'_, i32>) {
    // `r` has a shared reference, it is passed in as argument and hence
    // a barrier is added that marks this memory as read-only for the entire
    // duration of this function.
    drop(r);
    // *oops* here we can mutate that memory.
    *rc.borrow_mut() = 2;
}

#[analyzer::run]
pub fn main() {
    let rc = RefCell::new(0);
    break_it(&rc, rc.borrow())
}
