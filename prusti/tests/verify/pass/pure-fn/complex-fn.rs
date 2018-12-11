extern crate prusti_contracts;

struct A(i32);

struct T {
    a: (A, u32),
    f: bool,
    g: (u32, u32)
}

#[pure]
#[requires="-1000 < n && n < 1000"]
fn negative(n: i32) -> i32 {
    let x = T {
        a: (A(n), 0),
        f: false,
        g: (123, 456),
    };
    let new_a = A(-(x.a.0).0);
    let new_t = T {
        a: (new_a, 42),
        f: ! x.f,
        g: x.g
    };
    (new_t.a.0).0
}

#[ensures="forall i: i32 :: ( -1000 < i && i < 1000 ) ==> negative(i) == -i"]
fn main() {}
