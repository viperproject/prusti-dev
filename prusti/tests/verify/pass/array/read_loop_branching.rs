extern crate prusti_contracts;

fn sum_branching_simple_0(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        if sum >= 10 { i = 34 } else { i = i + 1 - 1 }
        sum += arr[i];
        i += 2;
    }
    sum
}

fn sum_branching_simple_1(arr: &[isize; 64]) -> isize {
    let mut i = 0;
    let mut sum = 0;
    while 0 <= i && i < 64 {
        if i >= 10 {
            sum += arr[i];
        }
        i += 1;
    }
    sum
}

fn sum_branching_simple_2(arr: &[isize; 64]) -> isize {
    let mut i = 0;
    let mut sum = 0;
    while 0 <= i && i < 64 {
        if i < 10 {
            sum += arr[i] + arr[i + 1] + arr[i + 2];
        } else if i < 20 {
            sum += arr[i] + arr[i + 42] + 20;
        } else {
            sum += arr[i];
        }
        i += 1;
    }
    sum
}

fn sum_branching_simple_3(arr: &[isize; 64]) -> isize {
    let mut i = 0;
    let mut sum = 0;
    while 0 <= i && i < 64 {
        if i < 10 {
            sum += arr[i] + arr[i + 1] + arr[i + 2];
        } else if i < 20 {
            sum += arr[i] + arr[i + 42] + 20;
        } else {
            sum += arr[i];
        }
        sum += arr[i];
        i += 1;
    }
    sum
}

fn sum_branching_complex(arr: &[isize; 64]) -> isize {
    let mut sum = 0;
    let mut i = 0;
    while 0 <= i && i < 64 {
        sum += arr[i];
        if arr[i] >= 10 {
            sum += arr[i] + arr[i - 5] + arr[i - 10];
        } else if arr[i] + 42 < -5 {
            sum += arr[i] + arr[i];
        } else {
            let mut ii = i - 32;
            if ii < 0 { ii = 42; }
            sum += arr[ii] + arr[i];
        }
        i += 2;
    }
    sum
}

fn main() {}