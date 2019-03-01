extern crate prusti_contracts;

#[requires="a + b <= std::u32::MAX"]
#[ensures="result == a + b"]
fn test(mut a: u32, mut b: u32) -> u32 {
    #[invariant="a + b == old(a + b)"]
    while a > 0 {
        a -= 1;
        b += 1;
    }
    b
}

fn main() {}
