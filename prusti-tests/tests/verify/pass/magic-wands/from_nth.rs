// compile-flags: -Pdisable_function_unfold_trigger=false

#![feature(box_patterns)]

use prusti_contracts::*;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

impl List {
    #[pure]
    #[ensures(result >= 1)]
    fn len(&self) -> usize {
        match self.next {
            None => 1,
            Some(box ref tail) => 1 + tail.len()
        }
    }
}

#[requires(0 <= n && n < r.len())]
#[ensures(result.len() == old(r.len()) - n)]
#[after_expiry(r.len() == n + before_expiry(result.len()))]
fn from_nth(r: &mut List, n: usize) -> &mut List {
    if n == 0 {
        r
    } else {
        match r.next {
            None => unreachable!(),
            Some(box ref mut tail) => from_nth(tail, n - 1)
        }
    }
}

fn main() {}
