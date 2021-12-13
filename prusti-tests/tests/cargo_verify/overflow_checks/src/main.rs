fn overflow_error(x: i32) -> i32 {
    x + 1
}

fn main() {
    let _ = overflow_error(123);
}
