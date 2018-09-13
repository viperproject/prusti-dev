extern crate prusti_contracts;

struct T {
    f: i32,
}

#[ensures="old(x.f) == result"]
fn extract(mut x: &mut T) -> i32 {
    // move x
    let y = x;
    let mut z = T { f: 42 };
    x = &mut z;
    y.f
}

fn main() {

}
