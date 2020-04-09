extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon; all but the last three succeed on Carbon.

fn sum_all(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        sum += arr[i];
        i += 1;
    }
    sum
}

fn sum_alternate(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        sum += arr[i];
        i += 2;
    }
    sum
}

fn sum_weird(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    let mut j = 0;
    while 0 <= i && i < arr.len() && 0 <= j && j < arr.len()  {
        sum += arr[i];
        sum += arr[j];
        i += 1;
        j += 3;
    }
    sum
}

fn sum_all_ref(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let a = &arr[i];
        i += 1;
        sum += *a;
    }
    sum
}

fn sum_alternate_ref(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let a = &arr[i];
        i += 2;
        sum += *a;
    }
    sum
}

fn sum_weird_ref(arr: &[isize]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    let mut j = 0;
    while 0 <= i && i < arr.len() && 0 <= j && j < arr.len()  {
        let a = &arr[i];
        let b = &arr[j];
        i += 1;
        j += 3;
        sum += *a + *b;
    }
    sum
}

fn main() {}