extern crate prusti_contracts;

fn test1(x: i32) {
    if x < 0 {
        test1(123); //~ ERROR please use a local variable as argument
    }
}

fn test2(x: i32) {
    if x < 0 {
        let c = 123;
        test2(c); // Ok
    }
}

fn main() {}
