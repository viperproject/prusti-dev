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
fn assign_same_array(arr: &mut [isize; 64], i: usize, j: usize) {
    arr[i] = arr[j];
}

// TODO: "ensures old(...)"
#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
fn swap_elements(arr: &mut [isize; 64], i: usize, j: usize) {
    let tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
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

fn assign_branching_simple(arr: &mut [usize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        //arr[i] = 0;
        if i >= 10 {
            arr[i] = 42;
        }
        i += 1;
    }
}

fn assign_branching_simple_2(arr: &mut [usize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        if i < 10 {
            arr[i] = 42;
        } else if i < 20 {
            arr[i] = i + 20;
        } else {
            arr[i] += 1;
        }
        i += 1;
    }
}

fn assign_branching_simple_3(arr: &mut [usize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        if i < 10 {
            arr[i] = 42;
        } else if i < 20 {
            arr[i] = i + 20;
        } else {
            arr[i] += 1;
        }
        arr[i] += 2;
        i += 1;
    }
}

fn assign_branching_simple_4(arr: &mut [usize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
        arr[i] += 3;
        if i < 10 {
            arr[i] = 42;
        } else if i < 20 {
            arr[i] = i + 20;
        } else {
            arr[i] += 1;
        }
        arr[i] += 2;
        i += 1;
    }
}

fn assign_many_times_branching(arr: &mut [isize; 64], from: isize) {
    let mut sum = from;
    let mut i = 0;
    while 0 <= i && i < 64 {
        let before = arr[i];
        arr[i] = sum;
        sum += before;
        arr[i] += sum;
        if arr[i] >= 10 {
            arr[i] = 0;
        } else if arr[i] + 42 < -5 {
            arr[i] *= 42;
        } else {
            let mut ii = i - 32;
            if ii < 0 { ii = 42; }
            let tmp = arr[ii];
            arr[ii] = arr[i];
            arr[i] = tmp;
        }
        i += 2;
    }
}

#[requires = "0 <= from && from < 64"]
#[requires = "0 <= to && to < 64"]
#[requires = "from <= to"]
fn partial_assign(arr: &mut [isize; 64], from: usize, to: usize, value: isize) {
    let mut i = from;
    #[invariant="0 <= i && i < 64"]
    while i < to {
        arr[i] = value;
        i += 1;
    }
}

/*
// TODO: these two fail
#[requires = "0 <= from && from < 64"]
#[requires = "0 <= to && to < 64"]
#[requires = "from <= to"]
fn array_copy(src: &[isize; 64], dst: &mut [isize; 64], from: usize, to: usize) {
    let mut i = from;
    #[invariant="0 <= i && i < 64"]
    while i < to {
        dst[i] = src[i];
        i += 1;
    }
}

fn assign_nested(arr: &mut [isize; 64]) {
    let mut i = 0;
    while i < 64 {
        let mut j = 0;
        while j < 64 {
            arr[i] = arr[j];
            j += 1;
        }
        i += 1;
    }
}
*/
fn main() {}