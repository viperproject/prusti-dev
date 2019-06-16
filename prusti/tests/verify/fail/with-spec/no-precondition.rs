extern crate prusti_contracts;

#[ensures="match result { 4 => false, _ => true}"]
fn foo(x: i64, y: bool) -> i64 { //~ ERROR postcondition might not hold
    let mut return_value = x * x;

    // ...code...

    if y && x == 4 {
        return_value = -999; // <-- bug
    }

    // ...more code...

    return_value
}

fn foo2(x: i64, y: bool) -> i64 {
    let mut return_value = x * x;

    // ...code...

    if y && x == 4 {
        return_value = -999; // <-- bug
    }

    // ...more code...

    assert!(return_value >= 0);  //~ ERROR assert!(..) statement might not hold
    return_value
}

fn main() {}
