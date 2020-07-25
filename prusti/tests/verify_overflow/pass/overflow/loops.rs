extern crate prusti_contracts;

#[requires="a + b <= std::u32::MAX"]
#[ensures="result == a + b"]
fn test(a: u32, b: u32) -> u32 {
    let mut c = a;
    let mut d = b;
    #[invariant="c > 0 && c + d == old(a + b)"]
    while c > 0 {
        c -= 1;
        d += 1;
    }
    d
}

fn main() {}
