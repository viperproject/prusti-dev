extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon, but all succeed on Carbon.

fn return_fixed(arr: &[isize; 64]) -> isize {
    arr[1]
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < 64"]
fn return_nth(arr: &[isize; 64], i: usize) -> isize {
    arr[i]
}

#[requires="0 <= i && i < 64"]
fn return_nth_from_ref(arr: &[isize; 64], i: usize) -> isize {
    let a = &arr[i];
    *a
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn sum_many(arr: &[isize; 64], i: usize, j: usize, k: usize) -> isize {
    arr[i] + arr[j] + arr[k]
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn sum_many_from_ref(arr: &[isize; 64], i: usize, j: usize, k: usize) -> isize {
    let a = &arr[i];
    let b = &arr[j];
    let c = &arr[k];
    *a + *b + *c
}

// With &mut

fn return_fixed_mut(arr: &mut [isize; 64]) -> isize {
    arr[1]
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < 64"]
fn return_nth_mut(arr: &mut [isize; 64], i: usize) -> isize {
    arr[i]
}

#[requires="0 <= i && i < 64"]
fn return_nth_from_ref_mut(arr: &mut [isize; 64], i: usize) -> isize {
    let a = &arr[i];
    *a
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn sum_many_mut(arr: &mut [isize; 64], i: usize, j: usize, k: usize) -> isize {
    arr[i] + arr[j] + arr[k]
}

#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn sum_many_from_ref_mut(arr: &mut [isize; 64], i: usize, j: usize, k: usize) -> isize {
    let a = &arr[i];
    let b = &arr[j];
    let c = &arr[k];
    *a + *b + *c
}

fn main() {}