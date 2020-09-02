extern crate prusti_contracts;

fn borrow(_x: &i32) {}

#[ensures="*n == old(*n)"]
pub fn test1(n: &mut i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        i += 1;
        cond = i < *n;
    }
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[ensures="*n == old(*n)"]
pub fn test2(n: &mut i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
    }
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[ensures="*n == old(*n)"]
pub fn test2_1(n: &mut i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
        assert!(false); //~ ERROR the asserted expression might not hold
    }
}

#[ensures="*n == old(*n)"]
pub fn test3(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
    }
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[ensures="*n == old(*n)"]
pub fn test3_1(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
        assert!(false); //~ ERROR the asserted expression might not hold
    }
}

#[requires="*n >= 0"]
#[ensures="*n == old(*n)"]
pub fn test4(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    #[invariant="i == 0"] //~ ERROR loop invariant might not hold after a loop iteration
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
    }
}

#[requires="*n >= 0"]
#[ensures="*n == old(*n)"]
pub fn test4_1(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    #[invariant="cond == (i < *n)"]
    #[invariant="0 <= i && i <= *n"]
    while cond {
        assert!(false); //~ ERROR the asserted expression might not hold
        i += 1;
        borrow(n);
        cond = i < *n;
    }
}

#[requires="*n >= 0"]
#[ensures="*n == old(*n)"]
pub fn test4_2(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    #[invariant="cond == (i < *n)"]
    #[invariant="0 <= i && i <= *n"]
    while cond {
        i += 1;
        borrow(n);
        cond = i < *n;
    }
    assert!(false); //~ ERROR the asserted expression might not hold
}

fn main() {
}
