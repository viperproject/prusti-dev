pub enum Void {}

pub fn unreachable_mut(x: &mut Void) -> ! {
    match *x {}
}

fn main() {}
