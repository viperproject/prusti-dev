extern crate prusti_contracts;

fn assign_branching_simple_0(arr: &mut [isize; 65], from: isize) {
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

fn assign_branching_simple_1(arr: &mut [usize; 64]) {
    let mut i = 0;
    while 0 <= i && i < 64 {
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

fn main() {}