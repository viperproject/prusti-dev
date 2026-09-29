use prusti_contracts::*;

pub struct Wrap<T> {
    pub t: T,
}

#[ensures(*result === *old(&w.t))]
#[after_expiry(Ghost::new_ref(&w.t) == before_expiry(Ghost::new_ref(&*result)))]
fn get_mut<T>(w: &mut Wrap<T>) -> &mut T {
    &mut w.t
}

fn use_get_mut() {
    let mut w = Wrap { t: 1i32 };
    let r = get_mut(&mut w);
    *r = 5;
    assert!(w.t == 5);
}
