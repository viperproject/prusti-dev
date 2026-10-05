use prusti_contracts::*;

pub fn f(n: usize) {
    let x = ((String::new(), 1), (2, 5));
    let _y = x.0.0;
    let mut i = 0;
    loop {
        body_invariant!(x.1.1 == 5);
        if i >= n {
            break;
        }
        i += 1;
    }
}
