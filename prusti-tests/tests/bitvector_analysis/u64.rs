fn main() {
    let x: u64 = 0x10000000;
    let y: u64 = 0xffffffff;

    assert!(x & y == x);
}