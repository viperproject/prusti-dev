#[allow(dead_code)]
#[allow(unused_variables)]

use prusti_contracts::*;

struct T0 (u32);

struct T1 {
    f: T0,
    g: u32,
    h: u32,
}

enum T2 {
    E2a(),
    E2b(u32),
    E2c(T1),
    E2d {
        f: T1,
        g: T1,
        h: T1,
    }

}

struct T3 {
    f: T1,
    g: T2,
    h: T2,
}

fn test2(x: T3, y: T2) {
    let mut x = x;
    if let T2::E2c(T1 { f: z, .. }) = x.g {}
    x.g = y;
}

#[derive(Clone, Copy)]
struct S1 {
    a: u32,
    b: u32,
}

#[derive(Clone, Copy)]
enum E1 {
    V1(u32),
    V2((u32, u32)),
    V3(S1),
    V4(u32),
}

fn test3(x: E1) -> E1 {
    let y = x;
    match x {
        E1::V1(x_val) => {
            if let E1::V1(y_val) = y {
                assert!(x_val == y_val);
            } else {
                unreachable!();
            }
        },
        _ => {},
    }
    y
}

struct S2 {
    f: u32,
    g: S1,
}

#[ensures(result.f == result.g.b)]
fn test4() -> S2 {
    S2 {
        f: 3,
        g: S1 {
            a: 4,
            b: 3,
        },
    }
}

#[pure]
fn get_f(s: &S2) -> u32 {
    s.f
}

#[pure]
fn get_b(s: &S1) -> u32 {
    s.b
}

#[ensures(get_f(&result) == get_b(&result.g))]
fn test5() -> S2 {
    S2 {
        f: 3,
        g: S1 {
            a: 4,
            b: 3,
        },
    }
}

struct NotUsed {
    f: T1,
    g: T2,
    h: T2,
}

/*
fn get_t2() -> T2 {
    unimplemented!();
}
*/

/* TODO: Uncomment this when we have support for loops with complex heads.
fn _test2(x: T3) {
    let mut curr = x;
    while let T2::E2c(T1 { f: z, .. }) = curr.g {
        curr.g = get_t2();
    }
}
*/

fn main() {}
