extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon, but all succeed on Carbon.

#[requires="0 <= i && i < 64"]
fn read_branching_simple_1(arr: &[isize; 64], i: usize) -> isize {
    let mut sum = 0;
    if i >= 10 {
        sum += arr[i];
    }
    sum
}

#[requires="0 <= i && i < 64"]
fn read_branching_simple_2(arr: &[isize; 64], i: usize) -> isize {
    let mut sum = 0;
    if i >= 10 {
        sum += arr[i];
    } else {
        sum -= arr[i];
    }
    sum
}

#[requires="0 <= i && i < 64"]
fn read_branching_simple_1_ref(arr: &[isize; 64], i: usize) -> isize {
    let mut sum = 0;
    if i >= 10 {
        let a = &arr[i];
        sum += *a;
    }
    sum
}

#[requires="0 <= i && i < 64"]
fn read_branching_simple_2_ref(arr: &[isize; 64], i: usize) -> isize {
    let mut sum = 0;
    if i >= 10 {
        let a = &arr[i];
        sum += *a;
    } else {
        let a = &arr[i];
        sum -= *a;
    }
    sum
}

fn main() {}