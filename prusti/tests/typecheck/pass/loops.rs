extern crate prusti_contracts;

struct T(u32);

struct A {
    f: T,
    g: T,
}

struct B {
    f: A,
    g: A,
}

fn main() {
    let mut c = true;
    let mut x = B {
        f: A { f: T(1), g: T(2) },
        g: A { f: T(3), g: T(4) },
    };
    if c {
        let y = x.f.g;
    }
    while c {
        c = false;
        let mut c2 = false;
        let _y = x.f.f.0;
        while c2 {
            x.g.g = T(1);
            c2 = true;
        }
    }
}

fn test() {
    let mut c = true;
    let mut x = B {
        f: A { f: T(1), g: T(2) },
        g: A { f: T(3), g: T(4) },
    };
    if c {
        let y = x.f.g;
    }
    while c {
        c = false;
        x.f.g = T(5);
        let _y = &mut x;
    }
}
