#![feature(core_intrinsics, rustc_attrs)]

struct Foo(i32);

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/main/main.dot")]
fn main() {
    let mut a = Foo(1);
    let mut b = Foo(1);

    let mut x = &mut a;
    let mut y = &mut b;

    let mut i = 10;
    while i > 1 {
        i -= 1;
        let tmp = x;
        x = y;
        y = tmp;
    }
}

struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/to_refs/to_refs.dot")]
fn to_refs<'a, T>(node: &'a mut Node<T>) -> Node<&'a mut T> {
    let mut result = Node { value: &mut node.value, next: None };
    let mut next = &mut node.next;
    while let Some(next_node) = next {
        result = Node { value: &mut next_node.value, next: Some(Box::new(result)) };
        next = &mut next_node.next;
    }
    drop(next);
    assert!(true);
    result
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/overwrite/overwrite.dot")]
fn overwrite() {
    let mut a = 10;
    let mut b = 20;

    assert!(1 == 1);

    let mut x = &mut a;

    assert!(2 == 2);

    *x = 10;
    x = &mut b;

    assert!(3 == 3);

    a = 2;

    let z = a + *x;
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/overwrite_2/overwrite.dot")]
fn overwrite_2() {
    let mut a = 10;
    let mut b = 20;

    assert!(1 == 1);

    let mut x = &mut a;
    let mut y = &mut *x;
    let mut z = &mut *y;

    assert!(2 == 2);

    y = &mut b;

    assert!(3 == 3);

    *z = 11;
    *y = 12;
}
