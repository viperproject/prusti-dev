fn main() {
    let a = abs(-1);
    let b = abs(1);

    let c = a + b;
}

fn abs(x: i32) -> i32 {
    let y: i32;
    if x >= 0 {
        y = x;
    }
    else {
        y = 0;
    }

    return y;
}