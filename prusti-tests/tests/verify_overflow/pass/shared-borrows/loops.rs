use prusti_contracts::*;

fn borrow(_x: &i32) {}

#[ensures(*n == old(*n))]
pub fn test1(n: &mut i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        body_invariant!(cond == (i < *n));
        body_invariant!(cond);  // issue: https://github.com/viperproject/prusti-dev/issues/448
        i += 1;
        cond = i < *n;
    }
}

#[ensures(*n == old(*n))]
pub fn test2(n: &mut i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        body_invariant!(cond == (i < *n));
        body_invariant!(cond);  // issue: https://github.com/viperproject/prusti-dev/issues/448
        i += 1;
        borrow(n);
        cond = i < *n;
    }
}

#[ensures(*n == old(*n))]
pub fn test3(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        body_invariant!(cond == (i < *n));
        body_invariant!(cond);  // issue: https://github.com/viperproject/prusti-dev/issues/448
        i += 1;
        borrow(n);
        cond = i < *n;
    }
}

#[requires(*n >= 0)]
#[ensures(*n == old(*n))]
pub fn test4(n: &i32) {
    let mut i = 0;
    let mut cond = i < *n;
    while cond {
        body_invariant!(cond == (i < *n));
        body_invariant!(0 <= i && i <= *n);
        body_invariant!(cond);  // issue: https://github.com/viperproject/prusti-dev/issues/448
        i += 1;
        borrow(n);
        cond = i < *n;
    }
}

fn main() {
}
