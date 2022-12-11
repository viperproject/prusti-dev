use prusti_contracts::*;

fn main() {
    let value = 42;
    assert!(value.combine(5) == 47);
    assert!(value.combine(true) == 42);
    assert!(value.combine(false) == 0);
}

trait Combine<T> {
    fn combine(&self, other: T) -> Self;
}

impl Combine<i32> for i32 {
    fn combine(&self, other: i32) -> Self {
        self + other
    }
}

impl Combine<bool> for i32 {
    fn combine(&self, other: bool) -> Self {
        if other { *self } else { 0 }
    }
}

#[extern_spec]
impl Combine<i32> for i32 {
    #[ensures(result == *self + other)]
    fn combine(&self, other: i32) -> Self;
}

#[extern_spec]
impl Combine<bool> for i32 {
    #[ensures(result == if other { *self } else { 0 })]
    fn combine(&self, other: bool) -> Self;
}
