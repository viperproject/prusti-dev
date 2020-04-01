extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon; all but the last three succeed on Carbon.

fn sum_all(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        sum += arr[i];
        i += 1;
    }
    sum
}

fn sum_alternate(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        sum += arr[i];
        i += 2;
    }
    sum
}

fn sum_weird(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    let mut j = 0;
    while 0 <= i && i < 64 && 0 <= j && j < 64  {
        sum += arr[i];
        sum += arr[j];
        i += 1;
        j += 3;
    }
    sum
}

fn sum_all_ref(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        let a = &arr[i];
        i += 1;
        sum += *a;
    }
    sum
}

fn sum_alternate_ref(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        let a = &arr[i];
        i += 2;
        sum += *a;
    }
    sum
}

fn sum_weird_ref(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    let mut j = 0;
    while 0 <= i && i < 64 && 0 <= j && j < 64  {
        let a = &arr[i];
        let b = &arr[j];
        i += 1;
        j += 3;
        sum += *a + *b;
    }
    sum
}

// TODO: this one fails because we do not preserve information about `arr`
/*
#[requires = "0 <= from && from <= 64"]
#[requires = "0 <= to && to <= 64"]
#[requires = "from <= to"]
fn partial_sum(arr: &[isize; 64], from: usize, to: usize) -> isize {
    let mut i = from;
    let mut ok = i < to;
    let mut sum = 0;
    #[invariant="0 <= i && i <= to"]
    #[invariant="ok ==> i < to"]
    #[invariant="!ok ==> i == to"]
    while ok {
        sum += arr[i];
        i += 1;
        ok = i < to;
    }
    sum
}
*/

// TODO: this one cause a crash, likely due to partial support of abrupt loop termination
// (replacing the array by a struct causes the same crash)
/*
fn sum_all_mut_1(arr: &mut [isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    #[invariant="i >= 0"]
    while i < 64 {
        sum += arr[i];
        i += 1;
    }
    sum
}
*/
// TODO: this attempt to fix sum_all_mut_1 results in lack of permission when exhaling old(arr)
/*
fn sum_all_mut_2(arr: &mut [isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    #[invariant="i >= 0"]
    while i < 64 {
        sum += arr[i];
        i += 1;
    }
    sum
}
*/

fn main() {}