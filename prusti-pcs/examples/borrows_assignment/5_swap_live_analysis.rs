struct K {d: u32}

#[analyzer::run]
fn main() {
    let mut x = &mut K {d: 0};
    let mut y = &mut K {d: 0};
    let tmp = x;
    x = y;
    y = tmp;
    let bx = x;
    let by = y;
}
