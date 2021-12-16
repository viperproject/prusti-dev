enum IntOption {
    Some(i32),
    None
}

fn foo(x: IntOption) -> i32 {
    let y = IntOption::Some(123);
    match x {
        IntOption::Some(y) => y,
        IntOption::None => 456
    }
}

fn main() {

}
