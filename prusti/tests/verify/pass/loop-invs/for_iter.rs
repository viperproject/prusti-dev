extern crate prusti_contracts;

// ignore-test closures are not supported

fn test() {
    let mut sum = 0;
    for i in (0..128).filter(|x| x % 3 == 0) {
        sum += i;
    }
}

fn main() {}
