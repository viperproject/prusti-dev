use prusti_contracts::*;

#[requires(a + b <= std::u32::MAX)]
#[ensures(result == a + b)]
pub fn test1(a: u32, b: u32) -> u32 {
    let mut c = a;
    let mut d = b;
    while c > 0 {
        body_invariant!(c > 0 && c + d == old(a + b));
        c -= 1;
        d += 1;
        assert!(false); //~ ERROR
    }
    d
}

#[requires(a + b <= std::u32::MAX)]
#[ensures(result == a + b)]
pub fn test2(a: u32, b: u32) -> u32 {
    let mut c = a;
    let mut d = b;
    while c > 0 {
        body_invariant!(c > 0 && c + d == old(a + b));
        c -= 1;
        d += 1;
    }
    assert!(false); //~ ERROR
    d
}

#[requires(a + b <= std::u32::MAX)]
#[ensures(result == b)] //~ ERROR
pub fn test3(a: u32, b: u32) -> u32 {
    let mut c = a;
    let mut d = b;
    while c > 0 {
        body_invariant!(c > 0 && c + d == old(a + b));
        c -= 1;
        d += 1;
    }
    d
}

fn main() {}
