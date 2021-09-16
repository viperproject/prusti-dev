fn main() {
    let x: u32 = 0x1000;
    let y: u32 = 0xffff;

    assert!(x & y == x);
}