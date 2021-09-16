fn main() {
    let x:u8 = !(1 & 1);
    assert!(x == 0xfe);
}