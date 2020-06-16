extern crate prusti_contracts;

struct T {
    f: u32,
}

struct H {
    g: T,
}

#[requires="a.g.f < 5"]
#[ensures="result.f == 5"]
fn test1(a: H) -> T {
    let mut a = a;
    let mut cont = true;
    #[invariant="a.g.f < 5"]
    #[invariant="cont == (a.g.f < 5)"]
    while cont {
        a.g.f += 1;
        cont = a.g.f < 5;
    }
    a.g
}

fn main() {}
