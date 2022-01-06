struct A {
    val: i32
}

struct B {
    val: bool
}

struct C {
    val: A
}

fn main() {
    let mut a = A { val: 111 };
    let mut b = B { val: true };
    let mut c = C { val: A { val: 222 } };
    a.val = 333;
    b.val = false;
    c.val.val = 444;
    assert!(a.val == 333);
    assert!(b.val == false);
    assert!(c.val.val == 444);
}
