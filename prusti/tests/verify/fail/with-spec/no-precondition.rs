extern crate prusti_contracts;

#[ensures="match result { 123 => false, _ => true}"] //~ ERROR postcondition might not hold
fn foo(x: i64, y: bool) -> i64 {
    let mut return_value = x * x;

    // ...code...

    if y && x == 82857399992 {
        return_value = -999; // <-- bug
    }

    // ...more code...

    assert!(return_value >= 0);
    return_value
}

fn main() {}
