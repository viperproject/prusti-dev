pub struct S {
    pub v: i32,
}

fn consume_b(_s: S) -> bool {
    false
}

fn guard_then_shared_arm(k: u8, z: S) -> i32 {
    match k {
        0 if consume_b(z) => 1,
        0 | 1 | 2 => 2,
        _ => 3,
    }
}
