// compile-flags: -Punsafe_core_proof=true -Pverify_types=false

use prusti_contracts::*;

fn test1() {
    let mut a = 1;
    let b = &mut a;
    let _c = &mut *b;
    a = 3;
}

fn test2() {
    let mut a = 1;
    let b = &mut a;
    let c = &mut *b;
    *c = 3;
    assert!(a == 3);
}

fn test3() {
    let mut a = 1;
    let b = &mut a;
    let c = &mut *b;
    *c = 3;
    assert!(a == 4);    //~ ERROR: the asserted expression might not hold
}

struct T1 {
    f: i32,
}

struct T2 {
    g: ((T1, T1), T1),
}

struct T3 {
    h: (T2, T2),
}

fn test4(mut a: T3) {
    let b = &mut a;
    let c = &mut b.h.1.g.0;
    let d = &mut c.1.f;
    *d = 4;
    assert!(a.h.1.g.0.1.f == 4);
}

fn test5(mut a: T3) {
    let b = &mut a;
    let c = &mut b.h.1.g.0;
    let d = &mut c.1.f;
    *d = 4;
    assert!(a.h.1.g.0.1.f == 5);    //~ ERROR: the asserted expression might not hold
}

struct T4<'a> {
    f: &'a mut T3,
}

fn test6(mut a: T3, b: T3) {
    let x = &mut a;
    let z = T4 {
        f: x,
    };
    let c = &mut z.f.h.1.g.0;
    let d = &mut c.1.f;
    *d = 4;
    assert!(a.h.1.g.0.1.f == 5);    //~ ERROR: the asserted expression might not hold
}

fn callee<'a>(a: &'a mut T3) -> T4<'a> {
    T4 {
        f: a,
    }
}

fn test7(mut a: T3, b: T3) {
    let x = &mut a;
    let z = callee(x);
    let _d = z;
}

struct T5<'a> {
    g: &'a T3,
}

fn test8(mut a: T3, b: T3) {
    let y = &b;
    let z = T5 {
        g: y,
    };
}

// FIXME:
//struct T5<'a, 'b> {
    //f: &'b mut T4<'a>,
    //g: &'b T4<'a>,
//}

fn main() {}
