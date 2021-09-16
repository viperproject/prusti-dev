fn main() {
    let x: u128 = 0x1000000000000000;
    let y: u128 = 0xffffffffffffffff;

    assert!(x & y == x);
}