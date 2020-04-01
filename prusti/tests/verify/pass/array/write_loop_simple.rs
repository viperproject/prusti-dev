extern crate prusti_contracts;

// ignore-test Some tests fail on Silicon, but all succeed (except the two last) on Carbon.

fn assign_all(arr: &mut [isize; 64], value: isize) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        arr[i] = value;
        i += 1;
    }
}

fn assign_alternate(arr: &mut [isize; 65], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < 65 {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        i += 2;
    }
}

fn initialize_to_42(arr: &mut [isize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        arr[i] = 42;
        i += 1;
    }
}

fn assign_many_times(arr: &mut [isize; 64], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < 64 {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        arr[i] += sum;
        i += 2;
    }
}

#[requires = "0 <= from && from <= 64"]
#[requires = "0 <= to && to <= 64"]
#[requires = "from <= to"]
fn partial_assign(arr: &mut [isize; 64], from: usize, to: usize, value: isize) {
    let mut i = from;
    let mut ok = i < to;
    #[invariant="0 <= i && i <= to"]
    #[invariant="ok ==> i < to"]
    #[invariant="!ok ==> i == to"]
    while ok {
        arr[i] = value;
        i += 1;
        ok = i < to;
    }
}

// TODO: these two take too much time to verify
/*
#[requires = "0 <= from && from <= 64"]
#[requires = "0 <= to && to <= 64"]
#[requires = "from <= to"]
fn array_copy(src: &[isize; 64], dst: &mut [isize; 64], from: usize, to: usize) {
    let mut i = from;
    let mut ok = i < to;
    #[invariant="0 <= i && i <= to"]
    #[invariant="ok ==> i < to"]
    #[invariant="!ok ==> i == to"]
    while ok {
        dst[i] = src[i];
        i += 1;
        ok = i < to;
    }
}

fn assign_nested(arr: &mut [isize; 64]) {
    let mut i = 0;
    #[invariant="0 <= i && i <= 64"]
    while i < 64 {
        let mut j = 0;
        #[invariant="0 <= j && j <= 64"]
        while j < 64 {
            arr[i] = arr[j];
            j += 1;
        }
        i += 1;
    }
}
*/
fn main() {}