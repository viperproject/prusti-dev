#![feature(box_patterns)]

struct Node {
    value: u32,
    next: Option<Box<Node>>
}

#[analyzer::run]
fn borrow_fields(mut head: Node) {
    let _val = &mut head.value;
    let _next = &head.next;
    noop();
}

#[analyzer::run]
fn last_val_mut(node: &mut Node) -> &mut u32 {
    let mut curr = node;
    while let Some(box next) = &mut curr.next {
        curr = next;
    }
    &mut curr.value
}

#[analyzer::run]
fn modify_last_val(head: &mut Node) {
    let first = &mut *head;
    let val = last_val_mut(first);
    *val = 123;
    noop();
}

#[analyzer::run]
fn noop() {}

fn main() {}
