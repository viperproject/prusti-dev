pub enum Void {}

pub fn unreachable_ref(x: &Void) -> ! {
    match *x {}
}

fn main() {}
