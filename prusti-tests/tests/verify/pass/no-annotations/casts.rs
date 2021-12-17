fn foo(a: u8, b: i8, c: usize, d: isize) {
    assert!(a as char as u8 as u16 as u32 as u64 as u128 == a as u128);
    assert!(b as i8 as i16 as i32 as i64 as i128 == b as i128);
    assert!(c as usize == c);
    assert!(d as isize == d);
}

fn main() {}
