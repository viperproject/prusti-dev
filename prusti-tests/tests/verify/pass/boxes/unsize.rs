use prusti_contracts::*;

fn unsize() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    assert!(b.len() == 3);
    assert!(b[0] == 1 && b[2] == 3);
}

fn unsize_mut() {
    let mut b: Box<[i32]> = Box::new([1, 2, 3]);
    b[1] = 9;
    assert!(b[1] == 9 && b[0] == 1);
}

#[requires(b.len() == 3)]
#[requires(b[0] == 1)]
#[ensures(b[0] == 2)]
#[ensures(b.len() == old(b.len()))]
fn incr_first(b: &mut Box<[i32]>) {
    b[0] = 2;
}

fn call_incr_first() {
    let mut b: Box<[i32]> = Box::new([1, 2, 3]);
    incr_first(&mut b);
    assert!(b[0] == 2);
}
