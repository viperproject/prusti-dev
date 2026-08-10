use prusti_contracts::*;

#[extern_spec]
impl<T> Box<T> {
    #[trusted]
    #[ensures(*result === value)]
    fn new(value: T) -> Box<T>;
}

fn main() {
    let x = Box::new(42);
    assert!(*x == 42);

    let y = Some(Box::new(72));
    match y {
        Some(n) => assert!(*n == 72),
        None => assert!(false),
    }
}
