extern crate prusti_contracts;
use prusti_contracts::*;

struct Foo {
    bar: i32,
    r#type: i32
}

#[requires(foo.bar == 1)]
fn check_bar_fn(foo: &Foo) {
}

#[requires(foo.r#type == 1)]
fn check_rtype_fn(foo: &Foo) {
}

fn main(){
}
