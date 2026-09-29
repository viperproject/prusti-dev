use prusti_contracts::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(*result == s.a)]
#[after_expiry(s.a == 42)] //~ERROR: pledge
fn get_a<'a>(s: &'a S) -> &'a i32 {
    &s.a
}
