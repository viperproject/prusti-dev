struct T1 {
    f: u32,
    g: u32,
    h: u32,
}

struct T2 {
    f: T1,
    g: T1,
    h: T1,
}

struct T3 {
    f: T1,
    g: T2,
    h: T2,
}

fn use_t3(_x: T3) {}

fn _test1(x: T3) {
    let z = x.f;
}

fn _test2(b: bool, mut x: T3, y: T1) {
    if b {
        let z = x.f;
    }
    x.f = y;
    use_t3(x);
}

fn _test3(mut x: T3, y: T1) {
    x.f = y;
}

struct S1 {
    f: T1,
}

struct S2 {
    f: S1,
}

fn _test4(b: bool, mut x: S2, y: T1) {
    if b {
        let z = x.f.f;
    }
    x.f.f = y;
}

fn main() {}
