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

#[pure]
fn rtype_same(foo1: &Foo, foo2: &Foo) -> bool {
    foo1.r#type == foo2.r#type
}

fn main(){
}
