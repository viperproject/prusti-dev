#![feature(box_patterns)]
use prusti_contracts::*;

struct List {
    val: i32,
    next: Option<Box<List>>
}

impl List {
    #[pure]
    #[ensures(result > 0)]
    fn len(&self) -> usize {
        match self.next {
            None => 1,
            Some(box ref tail) => tail.len() + 1
        }
    }
}

#[ensures(result.len() == 1)]
fn make_leaf(v: i32) -> List {
    List { val: v, next: None }
}

#[ensures(a.len() == old(a.len()) + 1)]
fn append(a: &mut List, v: i32) {
    if let Some(box ref mut tail) = a.next {
        append(tail, v);
    } else {
        a.next = Some(Box::new(make_leaf(v)));
    }
}

fn client(a: &mut List, b: &mut List) {
    let old_len_a = a.len();
    let old_len_b = b.len();
    append(a, 100);
    assert!(a.len() == old_len_a + 1);
    assert!(b.len() == old_len_b);
}

fn main() {}
