fn main() {
    let x: u16 = 0x10;
    let y: u16 = 0xff;

    assert!(x & y == x);
}