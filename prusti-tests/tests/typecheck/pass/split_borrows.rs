use prusti_contracts::*;

struct T {}

fn use_t(_x: &mut T) {}

fn test(mut a: T, mut b: T, mut d: T, mut c: bool) {
    let mut x = &mut a;
    let mut y = &mut d;
    while c {
        if !c {
            x = y;
            y = &mut a;
            x = &mut b;
        }
        c = false;
    }
    use_t(x);
    use_t(y);
}

/*
fn test(mut a: T, mut b: T, mut d: T, mut c: bool) {
    let mut x = &mut a;
    let mut y = &mut d;
    while c {
        if !c {
            x = &mut b;
            y = &mut a;
        }
        c = false;
    }
    use_t(x);
    use_t(y);
}

fn test(mut a: T, mut b: T, mut c: bool) {
    let mut x = &mut a;
    while c {
        if !c {
            x = &mut b;
        }
        c = false;
    }
    use_t(x);
}
*/

fn main() {}
