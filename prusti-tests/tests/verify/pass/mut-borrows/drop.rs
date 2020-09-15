use prusti_contracts::*;

struct T { f: u32, }

fn consume_T(_a: T) {}

pub fn test1(cond: bool) {
    let mut a = 1;
    let mut b = 2;
    let x;
    if cond {
        x = &mut a;
    } else {
        x = &mut b;
    }
    *x = 3;
    if cond {
        assert!(a == 3);
        assert!(b == 2);
    } else {
        assert!(a == 1);
        assert!(b == 3);
    }
}

pub fn test2(cond: bool) {
    let mut a = 1;
    let mut b = 2;
    let x;
    if cond {
        x = &mut a;
    } else {
        x = &mut b;
    }
    let y = &mut *x;
    *y = 3;
    if cond {
        assert!(a == 3);
        assert!(b == 2);
    } else {
        assert!(a == 1);
        assert!(b == 3);
    }
}

pub fn test3(cond: bool) {
    let mut a = T{ f: 1 };
    let mut b = T{ f: 2 };
    let x;
    if cond {
        x = &mut a;
    } else {
        x = &mut b;
    }
    x.f = 3;

    if cond {
        assert!(a.f == 3);
        assert!(b.f == 2);
    } else {
        assert!(a.f == 1);
        assert!(b.f == 3);
    }
}

pub fn test4(cond: bool) {
    let mut a = T{ f: 1 };
    let mut b = T{ f: 2 };
    let c = T{ f: 4 };
    let x;
    if cond {
        x = &mut a;
        consume_T(c);
    } else {
        x = &mut b;
    }
    x.f = 3;

    if cond {
        assert!(a.f == 3);
        assert!(b.f == 2);
    } else {
        assert!(a.f == 1);
        assert!(b.f == 3);
    }
}

fn main() {}
