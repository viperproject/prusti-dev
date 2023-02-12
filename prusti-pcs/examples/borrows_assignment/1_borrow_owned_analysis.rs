struct K {d: u32}

#[analyzer::run]
fn main() {
    let mut x: K = K {d: 0};
    let _ = &mut x;
}
