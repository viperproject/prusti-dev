extern crate prusti_contracts;

#[ensures="false"] //~ ERROR postcondition
fn foo1(x: bool) {}

#[ensures="false && false"] //~ ERROR postcondition
fn foo2(x: bool) {}

#[ensures="!true"] //~ ERROR postcondition
fn foo3(x: bool) {}

#[ensures="!(true || x)"] //~ ERROR postcondition
fn foo4(x: bool) {}

#[ensures="!(false || true)"] //~ ERROR postcondition
fn foo5(x: bool) {}

#[ensures="!(x || !false)"] //~ ERROR postcondition
fn foo6(x: bool) {}

#[ensures="!(x || !x)"] //~ ERROR postcondition
fn foo7(x: bool) {}

#[ensures="true ==> false"] //~ ERROR postcondition
fn foo8(x: bool) {}

#[ensures="x || true ==> !(x || !x)"] //~ ERROR postcondition
fn foo9(x: bool) {}

fn main() {}
