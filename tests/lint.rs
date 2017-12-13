#![feature(custom_attribute)]
#![feature(attr_literals)]

struct MyStruct {
    field: i32,
}

#[requires="x!=0"]
#[ensures="result!=0"]
fn divide(x: i32) -> i32 {
    x
}

#[requires="0 < n && n < 10"]
#[ensures="result > 0"]
fn fib(mut n: i32) -> i32 {
    let mut i = 1;
    let mut j = 1;
    #[invariant="i > 0 && j > 0"]
    while n > 2 {
        let tmp = i + j;
        j = i;
        i = tmp;
        n -= 1;
    }
    i
}

fn main() {
    let mut my_struct = MyStruct { field: 0 };

    let value = &my_struct.field;
    if *value == 0 {
        my_struct.field = divide(my_struct.field);
        my_struct.field += fib(3);
    }
}
