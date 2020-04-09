extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon, but all succeed on Carbon.

#[requires="arr.len() > 1"]
fn return_fixed(arr: &[isize]) -> isize {
    arr[1]
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < arr.len()"]
fn return_nth(arr: &[isize], i: usize) -> isize {
    arr[i]
}

#[requires="0 <= i && i < arr.len()"]
fn return_nth_from_ref(arr: &[isize], i: usize) -> isize {
    let a = &arr[i];
    *a
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn sum_many(arr: &[isize], i: usize, j: usize, k: usize) -> isize {
    arr[i] + arr[j] + arr[k]
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn sum_many_from_ref(arr: &[isize], i: usize, j: usize, k: usize) -> isize {
    let a = &arr[i];
    let b = &arr[j];
    let c = &arr[k];
    *a + *b + *c
}

// With &mut

#[requires="arr.len() > 1"]
fn return_fixed_mut(arr: &mut [isize]) -> isize {
    arr[1]
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < arr.len()"]
fn return_nth_mut(arr: &mut [isize], i: usize) -> isize {
    arr[i]
}

#[requires="0 <= i && i < arr.len()"]
fn return_nth_from_ref_mut(arr: &mut [isize], i: usize) -> isize {
    let a = &arr[i];
    *a
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn sum_many_mut(arr: &mut [isize], i: usize, j: usize, k: usize) -> isize {
    arr[i] + arr[j] + arr[k]
}

#[requires="0 <= i && i < arr.len()"]
#[requires="0 <= j && j < arr.len()"]
#[requires="0 <= k && k < arr.len()"]
fn sum_many_from_ref_mut(arr: &mut [isize], i: usize, j: usize, k: usize) -> isize {
    let a = &arr[i];
    let b = &arr[j];
    let c = &arr[k];
    *a + *b + *c
}

fn main() {}