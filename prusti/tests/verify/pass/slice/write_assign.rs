extern crate prusti_contracts;

#[requires="arr.len() > 42"]
fn assigned_fixed_lit(arr: &mut [isize]) {
    arr[42] = 1234;
}

#[requires="arr.len() > 42"]
fn assign_fixed(arr: &mut [isize], value: isize) {
    arr[42] = value;
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < arr.len()"]
fn assign_nth(arr: &mut [isize], i: usize, value: isize) {
    arr[i] = value;
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn assign_many(arr: &mut [isize], i: usize, j: usize, k: usize, value: isize) {
    arr[i] = value;
    arr[j] = value;
    arr[k] = value;
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn assign_many_lit(arr: &mut [isize], i: usize, j: usize, k: usize) {
    arr[i] = 123;
    arr[j] = 456;
    arr[k] = 789;
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
#[requires="0 <= l && l < arr.len()"]
fn assign_self(arr: &mut [isize], i: usize, j: usize, k: usize, l: usize) {
    arr[i] = arr[j];
    arr[k] = arr[l];
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
fn assign_same_array(arr: &mut [isize], i: usize, j: usize) {
    arr[i] = arr[j];
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
fn swap_elements(arr: &mut [isize], i: usize, j: usize) {
    let tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}


fn main() {}