#![allow(dead_code)]
extern crate prusti_contracts;

mod foo {
    pub fn get_false() -> bool {
        false
    }
}

fn get_true() -> bool {
    true
}

#[requires="get_true() && !foo::get_false()"]
fn main() {
}
