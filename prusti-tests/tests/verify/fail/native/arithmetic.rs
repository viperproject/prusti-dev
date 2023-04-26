// compile-flags: -Pviper_backend=Lithium

fn test(m: i32, c: i32, d: i32) {
    assert!(m * c - m * d == m * (c - d + 1)); //~ ERROR might not hold
}

fn main() {}
