struct S1 {
    f: *const u32,
}

fn test1(x: S1) -> S1 {
    let y = x;
    y
}

struct S2 {
    f: String,
}

fn test2(x: S2) -> S2 {
    let y = x;
    y
}

fn main() {}
