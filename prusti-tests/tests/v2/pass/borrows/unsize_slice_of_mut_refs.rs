fn foo(_v: &mut [&mut i32]) {}

fn consume() {
    let mut x = 4_i32;
    let mut y = [&mut x];
    foo(&mut y);
}
