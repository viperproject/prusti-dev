/*
    This test is interesting because std::convert::From has many blanket implementations in the
    standard library. The verifier should however pick the specification from our implementation
    on Dummy (since it is the receiver of the method call).
 */
use prusti_contracts::*;

struct Dummy {
    value: u32,
}

#[refine_trait_spec]
impl std::convert::From<u32> for Dummy {
    #[ensures(result.value == val)]
    fn from(val: u32) -> Self {
        Dummy { value: val}
    }
}

fn main() {
    let d = Dummy::from(32);
    assert!(d.value == 32);
}