extern crate prusti_contracts;

struct T(u32);

fn random() -> bool { true }

fn consume(y: &mut T) { }

fn check_join(mut x: (T, T)) -> T {
    if random() {
        consume(&mut x.0)
    }
    x.1
}

fn main() {}
