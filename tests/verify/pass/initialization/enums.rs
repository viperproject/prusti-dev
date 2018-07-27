#![feature(nll)]

extern crate prusti_contracts;

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

fn _test1(x: T3, y: T2) {
    let mut x = x;
    if let T2::E2c(T1 { f: z, .. }) = x.g {}
    x.g = y;
}

fn get_t2() -> T2 {
    unimplemented!();
}

/* TODO: Uncomment.
fn _test2(x: T3) {
    let mut curr = x;
    while let T2::E2c(T1 { f: z, .. }) = curr.g {
        curr.g = get_t2();
    }
}
*/

fn main() {}
