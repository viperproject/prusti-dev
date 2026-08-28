pub enum Void {}

mod declaring {
    use super::Void;

    pub struct SecretlyVoid {
        _void: Void,
    }

    pub enum Either<T> {
        Value(T),
        Empty(SecretlyVoid),
    }
}

pub fn unwrap_outside<T>(this: declaring::Either<T>) -> T {
    match this {
        declaring::Either::Value(value) => value,
        declaring::Either::Empty(_) => unreachable!(),
    }
}

fn main() {}
