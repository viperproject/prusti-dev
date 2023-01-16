struct K {d: u32}

#[analyzer::run]
fn main() {
    let mut x: K = K {d: 0};
    let mut bx = &mut x;
    let x = &mut bx;
}
