#![feature(core_intrinsics, rustc_attrs)]

struct Node<T> {
    f: T,
    n: Option<Box<Node<T>>>,
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/smain/smain.dot")]
fn main() {
    let mut x = Node { f: 1, n: None };

    let b = &x;
    let a = &x.f;
    let c = Node { f: b, n: None };
    let r = foo(a, b, c);

    x.f = 2;
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/sfoo/sfoo.dot")]
fn foo<'a, T>(a: &'a T, b: &'a Node<T>, c: Node<&'a Node<T>>) -> Node<(&'a T, &'a Node<T>)> {
    let mut result = Node { f: (a, b), n: None };

    while nondet() {
        if nondet() {
            let new_result = Node {
                f: (a, b),
                n: Some(Box::new(result))
            };
            result = new_result;
        } else if nondet() {
            let new_result = Node {
                f: (&b.f, b),
                n: Some(Box::new(result))
            };
            result = new_result;
        } else if nondet() {
            let new_result = Node {
                f: (a, c.f),
                n: Some(Box::new(result))
            };
            result = new_result;
        } else {
            let new_result = Node {
                f: (&c.f.f, b),
                n: Some(Box::new(result))
            };
            result = new_result;
        }
    }
    result
}

#[inline(never)]
fn nondet() -> bool {
    todo!()
}
