use prusti_contracts::*;

#[ensures(*result == old(*x))]
fn reborrow(x: &u32) -> &u32 {
    x
}

pub fn test1() {
    let mut a = 5;
    let x = &a;
    let y = reborrow(x);
    assert!(a == 5);
    assert!(*x == 5);
    assert!(*y == 5);
    assert!(a == 5);
    a = 6;
    assert!(a == 6);
}

pub struct Vector {
    f: u32,
    g: u32,
}

#[pure]
#[requires(0 <= index && index < 2)]
pub fn is_equal(v: &Vector, index: usize, e: &u32) -> bool {
    if index == 0 {
        v.f == *e
    } else if index == 1 {
        v.g == *e
    } else {
        unreachable!()
    }
}


#[requires(0 <= index && index < 2)]
pub fn index_test(v: &Vector, index: usize) -> &u32 {
    if index == 0 {
        &v.f
    } else if index == 1 {
        &v.g
    } else {
        unreachable!()
    }
}

#[requires(0 <= index && index < 2)]
#[ensures(is_equal(v, index, result))]
#[trusted]  // TODO: Replace is_equal with the memory equality once we
            // have it implemented. The problem why we cannot use Rust
            // equality here is that v and index are from the pre-state
            // while result is from the post state and &u32 is not a
            // primitive Viper type.
pub fn index(v: &Vector, index: usize) -> &u32 {
    if index == 0 {
        &v.f
    } else if index == 1 {
        &v.g
    } else {
        unreachable!()
    }
}

#[ensures(match result {
            Some(index) => is_equal(v, index, e),
            None => true,
           })]
pub fn test9(v: &Vector, e: &u32) -> Option<usize> {
    if *index(v, 0) == *e {
        Some(0)
    } else if *index(v, 1) == *e {
        Some(1)
    } else {
        None
    }
}

pub fn convert(s: &mut u32) -> &u32 {
    s
}

pub fn convert2(s: &mut u32) -> &u32 {
    let x = &*s;
    x
}

fn main() {
}
