extern crate prusti_contracts;

struct T(u32);

fn random() -> bool { true }

fn consume(y: &mut T) { }

fn check_join(mut x: (T, T)) -> T {
    // We have both `x.0` and `x.1`
    if random() {
        // We move permission of `x.0` to consume
        consume(&mut x.0)
    }
    // After the join we would like to use `x.1`
    x.1
}

fn main() {}
