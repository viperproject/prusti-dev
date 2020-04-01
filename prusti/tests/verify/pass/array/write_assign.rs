extern crate prusti_contracts;

fn assigned_fixed_lit(arr: &mut [isize; 64]) {
    arr[42] = 1234;
}

fn assign_fixed(arr: &mut [isize; 64], value: isize) {
    arr[42] = value;
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < 64"]
fn assign_nth(arr: &mut [isize; 64], i: usize, value: isize) {
    arr[i] = value;
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn assign_many(arr: &mut [isize; 64], i: usize, j: usize, k: usize, value: isize) {
    arr[i] = value;
    arr[j] = value;
    arr[k] = value;
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn assign_many_lit(arr: &mut [isize; 64], i: usize, j: usize, k: usize) {
    arr[i] = 123;
    arr[j] = 456;
    arr[k] = 789;
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
#[requires="0 <= l && l < 64"]
fn assign_self(arr: &mut [isize; 64], i: usize, j: usize, k: usize, l: usize) {
    arr[i] = arr[j];
    arr[k] = arr[l];
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
fn assign_same_array(arr: &mut [isize; 64], i: usize, j: usize) {
    arr[i] = arr[j];
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
fn swap_elements(arr: &mut [isize; 64], i: usize, j: usize) {
    let tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}

// TODO: assign from &mut

fn main() {}