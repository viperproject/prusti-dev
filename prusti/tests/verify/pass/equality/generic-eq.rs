extern crate prusti_contracts;

#[derive(Clone)]
struct A<T> {
    i: i32,
    t: T,
}

impl PartialEq for A<i32> {
    fn eq(&self, other: &A<i32>) -> bool {
        self.i == other.i
    }
}

#[pure]
fn get_value<T>(_x: &A<T>) -> i32 {
    _x.i
}

#[ensures="result == 1"]
fn test_eq_in_code(_a: &A<i32>, _b: &A<i32>) -> i32 {
    if *_a == *_b {
        if get_value(_a) == get_value(_b) {
            1
        } else {
            0
        }
    } else {
        if _a == _b {
            2
        } else {
            1
        }
    }
}

fn main() {
}

