use prusti_contracts::*;

struct T {
    val: i32
}

fn mutate_local() {
    let mut a = T { val: 3 };
    let x = &mut a;
    x.val = 4;
    a.val = 5;
}

fn mutate_local_branch(c: bool) {
    let mut a = T { val: 3 };
    let mut b = T { val: 4 };
    let x;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
    x.val = 5;
    a.val = 6;
}

fn reborrow(x: &mut T) -> &mut i32 {
    &mut x.val
}

fn call_reborrow() {
    let mut a = T { val: 5 };
    let x = &mut a;
    let y = reborrow(x);
    *y = 4;
}

fn shared_reference() {
    let mut a = T { val: 3 };
    let x = &a;
    let _y = x.val;
}

fn main() {}

