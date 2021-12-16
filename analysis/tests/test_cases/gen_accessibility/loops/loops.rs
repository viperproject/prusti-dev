fn borrow(_x: &i32) {}

pub fn test(n: &i32) {
    let mut i = 0;
    while i < *n {
        i += 1;
        borrow(n);
    }
}
