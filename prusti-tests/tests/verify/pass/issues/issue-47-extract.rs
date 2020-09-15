use prusti_contracts::*;

struct T {
    f: i32,
}

#[ensures(x.f == result)]
#[ensures(old(x.f) == result)]
fn extract(x: &mut T) -> i32 {
    // move x
    let y = x;
    let mut z = T { f: 42 };
    let x = &mut z;
    y.f
}

fn main() {

}
