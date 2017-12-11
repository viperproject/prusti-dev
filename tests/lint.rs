#![feature(custom_attribute)]
#![feature(attr_literals)]


struct MyStruct {
    field: i32,
}

#[requires="x!=0"]
fn divide(x: i32) -> i32 {
    x
}

fn main() {
    let mut my_struct = MyStruct { field: 0 };

    let value = &my_struct.field;
    if *value == 0 {
        my_struct.field = divide(my_struct.field)
    }
}
