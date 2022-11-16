#![allow(dead_code)]
use prusti_contracts::*;

mod foo {
    pub fn get_false() -> bool {
        false
    }
}

fn get_true() -> bool {
    true
}

#[pure]
fn pure_get_true() -> bool {
    true
}

#[requires(get_true())]
fn foo() {}

#[requires(pure_get_true() && !foo::get_false())]
fn main() {}
