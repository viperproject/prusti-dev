/// Problem case #4: mutating &mut references
///
/// Adapted from
/// [here](https://github.com/nikomatsakis/nll-rfc/blob/master/0000-nonlexical-lifetimes.md).
///
/// TODO: Add specifications.

extern crate prusti_contracts;

struct List {
    value: i32,
    next: Option<Box<List>>,
}

fn get_last_value<T>(list: &mut List) -> &mut i32 {
    let mut list = list;
    let mut had_next = true;
    while had_next {
        if let Some(ref mut n) = list.next {
            list = n;
        } else {
            had_next = false;
        }
        list = list;
    }
    &mut list.value
}

fn main() {}
