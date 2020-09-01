#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

#[pure]
fn lookup(head: &List, index: usize) -> u32 {
    if index == 0 {
        head.value
    } else {
        match head.next {
            Some(box ref tail) => lookup(tail, index - 1),
            None => unreachable!()
        }
    }
}

#[pure]
fn len(head: &List) -> usize {
    match head.next {
        None => 1,
        Some(box ref tail) => 1 + len(tail)
    }
}

#[pure]
fn is_none(list: &mut Option<Box<List>>) -> bool {
    match list {
        None => true,
        Some(_) => false,
    }
}

#[pure]
fn is_some(list: &mut Option<Box<List>>) -> bool {
    match list {
        None => false,
        Some(_) => true,
    }
}

#[trusted]
fn random() -> bool {
    unimplemented!();
}

/// Returns the last node of the linked list. Recursive implementation.
#[ensures="is_none(&mut result.next)"]
#[ensures="result.value == old(lookup(head, len(head) - 1))"]
//#[ensures="
    //after_expiry<result>(
        //(forall i: usize :: {lookup(head, i)}
            //(0 <= i && i < old(len(head)) - 1) ==>
            //lookup(head, i) == old(lookup(head, i))) &&
        //(forall i: usize :: {lookup(result, i)}
            //(0 <= i && i < before_expiry(len(result))) ==>
            //lookup(head, old(len(head)) - 1 + i) == before_expiry(lookup(result, i))) &&
        //len(head) == old(len(head)) - 1 + before_expiry(len(result))
    //)
//"]
fn recursive_get_last(head: &mut List) -> &mut List {
    match head.next {
        None => head,
        Some(box ref mut next) => recursive_get_last(next)
    }
}

/// Returns the last node of the linked list. Iterative implementation.
#[ensures="is_none(&mut result.next)"]
#[ensures="result.value == old(lookup(head, len(head) - 1))"]
//#[ensures="
    //after_expiry<result>(
        //(forall i: usize :: {lookup(head, i)}
            //(0 <= i && i < old(len(head)) - 1) ==>
            //lookup(head, i) == old(lookup(head, i))) &&
        //(forall i: usize :: {lookup(result, i)}
            //(0 <= i && i < before_expiry(len(result))) ==>
            //lookup(head, old(len(head)) - 1 + i) == before_expiry(lookup(result, i))) &&
        //len(head) == old(len(head)) - 1 + before_expiry(len(result))
    //)
//"]
fn iterative_get_last<'a>(head: &'a mut List) -> &'a mut List {
    let mut curr = head;
    let mut has_next = is_some(&mut curr.next);
    //#[invariant="has_next == is_some(&mut curr.next)"]
    //#[invariant="curr.value == old(lookup(head, len(head) - len(curr)))"]
    //#[invariant="
        //after_expiry<curr>(
            //(forall i: usize :: {lookup(head, i)}
                //(0 <= i && i < old(len(head)) - 1) ==>
                //lookup(head, i) == old(lookup(head, i))) &&
            //(forall i: usize :: {lookup(curr, i)}
                //(0 <= i && i < before_expiry(len(curr))) ==>
                //lookup(head, old(len(head)) - 1 + i) == before_expiry(lookup(curr, i))) &&
            //len(head) == old(len(head)) - 1 + before_expiry(len(curr))
        //)
    //"]
    while has_next {
        curr = match curr.next {
            None => unreachable!(),
            Some(box ref mut next) => next
        };
        has_next = is_some(&mut curr.next);
    }
    curr
}

/// Appends a value at the end of a linked list
#[ensures="len(head) == old(len(head)) + 1"]
#[ensures="value == lookup(head, len(head) - 1)"]
//#[ensures="forall i: usize :: {lookup(head, i)}
            //(0 <= i && i < old(len(head))) ==>
            //lookup(head, i) == old(lookup(head, i))"]
fn append(head: &mut List, value: u32) {
    let last = iterative_get_last(head);
    assert!(last.next.is_none());
    last.next = Some(box List {
        next: None,
        value: value,
    });
}

fn conditional_reborrowing() {
    let mut a = 0;
    let mut b = 0;
    let mut x = &mut a;
    let mut condition = true;
    #[pure]
    let mut counter = 0;
    //#[invariant="after_expiry<x>(a + b == counter)"]
    while condition {
        if random() {
            x = &mut b;
        }
        *x += 1;
        counter += 1;
        if counter == 5 {
            condition = false;
        }
    }
    assert!(a + b == 5);
}

fn main() {}
