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
fn get_value<T>(x: &A<T>) -> i32 {
    x.i
}

#[ensures="result == 1"]
fn test_eq_in_code(a: &A<i32>, b: &A<i32>) -> i32 {
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

fn main() {
}

