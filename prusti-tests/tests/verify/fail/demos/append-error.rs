#![feature(box_patterns)]

use prusti_contracts::*;

struct List {
    val: i32,
    next: Option<Box<List>>,
}

impl List {
    #[pure]
    fn len(&self) -> usize {
        match self.next {
            None => 1,
            Some(box ref tail) => tail.len() + 1,
        }
    }
}

fn append(a: &mut List, v: i32) {
    if let Some(box ref mut tail) = a.next {
        append(tail, v);
    } else {
        a.next = Some(Box::new(List {
            val: v,
            next: None,
        }));
    }
}

fn client(a: &mut List, b: &mut List) {
    let old_len = b.len();
    append(a, 100);
    assert!(b.len() != old_len); //~ ERROR
}

fn main() {}
