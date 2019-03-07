extern crate prusti_contracts;

struct T { f: u32, }

pub fn test1(cond: bool) {
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

fn main() {}

