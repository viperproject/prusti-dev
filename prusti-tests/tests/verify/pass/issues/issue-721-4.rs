// compile-flags: -Pverification_deadline=5

fn main() {
    const SIZE: usize = 1_000_000;
    let array = [0u8; SIZE];
    assert!(array.len() == SIZE);
}
