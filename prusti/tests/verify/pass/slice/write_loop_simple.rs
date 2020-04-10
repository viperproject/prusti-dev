extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon, all but the last one succeed on Carbon.

fn assign_all(arr: &mut [isize], value: isize) {
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        arr[i] = value;
        i += 1;
    }
}

fn assign_alternate(arr: &mut [isize], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        i += 2;
    }
}

fn initialize_to_42(arr: &mut [isize]) {
    let mut i = 0;
    while 0 <= i && i < arr.len() {
        arr[i] = 42;
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
        arr[i] += sum;
        i += 2;
    }
}

// TODO: this one fails to verify
/*
#[requires = "0 <= from && from <= arr.len()"]
#[requires = "0 <= to && to <= arr.len()"]
#[requires = "from <= to"]
fn partial_assign(arr: &mut [isize], from: usize, to: usize, value: isize) {
    let mut i = from;
    let mut ok = i < to;
    #[invariant="0 <= i && i <= to"]
    #[invariant="0 <= i && i <= arr.len()"]
    #[invariant="ok ==> i < to"]
    #[invariant="ok ==> i < arr.len()"]
    #[invariant="!ok ==> i == to"]
    #[invariant="!ok ==> i <= arr.len()"]
    while ok {
        arr[i] = value;
        i += 1;
        ok = i < to;
    }
}
*/
fn main() {}