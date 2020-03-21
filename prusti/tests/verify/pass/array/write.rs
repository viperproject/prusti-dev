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

fn assign_weird(arr: &mut [isize; 65], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < 65 {
        if sum >= 10 { i = 34 } else { i = i + 1 - 1 }
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

fn main() {}