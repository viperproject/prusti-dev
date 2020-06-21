extern crate prusti_contracts;

#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(x: &A) -> i32 {
    x.i 
}

#[ensures="result == 1"]
fn test_eq_in_code(a: &A, b: &A) -> i32 {
    if *a == *b {
        if get_value(a) == get_value(b) {
            1
        } else {
            0
        }
    } else {
        if a == b { 
            2
        } else {
            1
        }
    }
}

fn test_construct_eq() {
    let a = A { i: 7 };
    let b = A { i: 7 };
    if a == b {
        if get_value(&a) == get_value(&b) {
        } else {
            panic!();
        }
    } else {
        panic!();
    }
}

#[requires="x == y"]
#[ensures="result == 2*get_value(x)"]
fn test_eq_propagation(x: &A, y: &A) -> i32 {
    get_value(x) + get_value(y)
}

