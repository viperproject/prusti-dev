fn main() {
    let n = 1;
    let x = match n {
        -1 => 123,
        0 => -1,
        1 => 1,
        2 => 42,
        _ => unreachable!()
    };
}
