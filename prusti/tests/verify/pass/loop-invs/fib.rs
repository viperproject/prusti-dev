extern crate prusti_contracts;

struct MyStruct {
    field: i32,
}

#[requires="0 < n"]
//#[ensures="result > 0"]
fn fib(n: i32) -> i32 {
    let mut k = n;
    let mut i = 1;
    let mut j = 1;
    #[invariant="i > 0 && j > 0"]
    while k > 2 {
        let tmp = i + j;
        j = i;
        i = tmp;
        k -= 1;
    }
    i
}

#[requires="true ==> forall x: i32, y45: usize ::  (x > 0 && y45 > 0) ==> y45 + 2 > 2"]
fn main() {
    let x = fib(10);
    //assert!(x != 0);
}
