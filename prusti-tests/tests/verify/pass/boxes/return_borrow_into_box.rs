use prusti_contracts::*;

#[ensures(*result == old(**b))]
#[after_expiry(**b == before_expiry(*result))]
fn deref_box(b: &mut Box<i32>) -> &mut i32 {
    &mut **b
}

fn use_after_expiry() {
    let mut b = Box::new(1);
    let r = deref_box(&mut b);
    assert!(*r == 1);
    *r = 5;
    assert!(*r == 5);
    assert!(*b == 5);
}

#[ensures(*result === *old(&**b))]
#[after_expiry(**b === *before_expiry(&*result))]
fn deref_box_generic<T>(b: &mut Box<T>) -> &mut T {
    &mut **b
}

fn use_after_expiry_generic() {
    let mut b = Box::new(1);
    let r = deref_box_generic(&mut b);
    assert!(*r == 1);
    *r = 5;
    assert!(*r == 5);
    assert!(*b == 5);
}
