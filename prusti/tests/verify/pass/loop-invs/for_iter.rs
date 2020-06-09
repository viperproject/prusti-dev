extern crate prusti_contracts;

fn test() {
    let mut sum = 0;
    for i in (0..128).filter(|x| x % 3 == 0) {
        sum += i;
    }
}

fn main() {}
