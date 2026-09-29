use prusti_contracts::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(*result == s.a)]
#[after_expiry(s.a == before_expiry(*result))]
fn get_a_ok<'a>(s: &'a S) -> &'a i32 {
    &s.a
}

fn use_ok() {
    let s = S { a: 1, b: 2 };
    let r = get_a_ok(&s);
    let x = *r;
    assert!(x == 1);
    assert!(s.a == 1);
}
