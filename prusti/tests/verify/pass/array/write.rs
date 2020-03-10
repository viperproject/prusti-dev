extern crate prusti_contracts;
/*
fn assign_fixed(arr: &mut [isize; 64], value: isize) {
    arr[42] = value;
}*/

// We need i >= 0 because unsigned integers bounds are not encoded by default
/*#[requires="0 <= i && i < 64"]
fn assign_nth(arr: &mut [isize; 64], i: usize, value: isize) {
    let mut val = value;
    let abc = arr[i];
    arr[i] = val;
    val += 1;
}*/

fn assign_all(arr: &mut [isize; 64], from: isize) {
    let mut sum = from;
    let mut i = 0;
    #[invariant="0 <= i && i < 64"]
    while 0 <= i && i < 64 {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        i += 1;
    }
}

/*
fn assign_alternate(arr: &mut [isize; 65], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < 65 {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        i += 2;
    }
}*/

fn main() {}