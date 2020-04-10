extern crate prusti_contracts;

// ignore-test

fn assigned_fixed_lit(arr: &mut [isize]) {
    arr[0] = 1234; //~ ERROR assertion might fail with "array index out of bounds"
}

fn assign_fixed(arr: &mut [isize], value: isize) {
    arr[0] = value; //~ ERROR assertion might fail with "array index out of bounds"
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < arr.len()"]
fn assign_nth(arr: &mut [isize], i: usize, value: isize) {
    arr[i + 1] = value; //~ ERROR assertion might fail with "array index out of bounds"
}

fn assign_all(arr: &mut [isize], value: isize) {
    let mut i = 0;
    while 0 <= i && i < arr.len() + 1 {
        arr[i] = value; //~ ERROR assertion might fail with "array index out of bounds"
        i += 1;
    }
}

fn assign_alternate(arr: &mut [isize], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let before = arr[i];
        arr[i-1] = sum; //~ ERROR assertion might fail with "array index out of bounds"
        sum += before;
        i += 2;
    }
}

fn assign_weird(arr: &mut [isize], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        if sum >= 10 { i = 34 } else { i = i + 1 }
        let before = arr[i]; //~ ERROR assertion might fail with "array index out of bounds"
        arr[i] = sum; //~ ERROR assertion might fail with "array index out of bounds"
        sum += before;
        i += 2;
    }
}

fn initialize_to_42(arr: &mut [isize]) {
    let mut i = 0;
    while 0 <= i && i <= arr.len() {
        arr[i] = 42; //~ ERROR assertion might fail with "array index out of bounds"
        i += 1;
    }
}

fn assign_many_times(arr: &mut [isize], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        i += 1;
        arr[i] += sum; //~ ERROR assertion might fail with "array index out of bounds"
        i += 2;
    }
}

fn assign_many_times_branching(arr: &mut [isize], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        arr[i] += sum;
        if arr[i] >= 10 {
            arr[i] = 0;
        } else if arr[i] + 42 < -5 {
            arr[i] *= 42;
        } else {
            let mut ii = i - 32;
            let tmp = arr[ii]; //~ ERROR assertion might fail with "array index out of bounds"
            arr[ii] = arr[i]; //~ ERROR assertion might fail with "array index out of bounds"
            arr[i] = tmp;
        }
        i += 2;
    }
}

fn main() {}