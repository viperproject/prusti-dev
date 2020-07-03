extern crate prusti_contracts;

struct T {
    f: i32,
}

fn rand() -> bool { true }

#[ensures="x.f == result"]
fn extract(x: &mut T) -> i32 {
    // `x` is moved to `y`
    let y = x;

    if rand() {
        // unfold `y`
        y.f
    } else {
        y.f = 123;
        // `y` is moved to `z`
        let z = y;
        123
    }
    // In Viper, `x` may be an alias of `z` or `y` (which has been unfolded)
}

fn main() {}
