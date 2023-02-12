struct K {d: u32}

#[analyzer::run]
fn main() {
    let mut v0 = K {d: 0};
    let mut v1 = K {d: 1};

    let mut x = &mut v0;
    let y = &mut (*x);
    x = &mut v1;

    let test_x = x;
    let test_y = y;
}
