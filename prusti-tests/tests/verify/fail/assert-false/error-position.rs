use prusti_contracts::*;

#[ensures(false)] //~ ERROR postcondition might not hold
fn foo1(x: bool) {}

#[ensures(false && false)] //~ ERROR postcondition might not hold
fn foo2(x: bool) {}

#[ensures(!true)] //~ ERROR postcondition might not hold
fn foo3(x: bool) {}

#[ensures(!(true || x))] //~ ERROR postcondition might not hold
fn foo4(x: bool) {}

#[ensures(!(false || true))] //~ ERROR postcondition might not hold
fn foo5(x: bool) {}

#[ensures(!(x || !false))] //~ ERROR postcondition might not hold
fn foo6(x: bool) {}

#[ensures(!(x || !x))] //~ ERROR postcondition might not hold
fn foo7(x: bool) {}

#[ensures(true ==> false)] //~ ERROR postcondition might not hold
fn foo8(x: bool) {}

#[ensures(x || true ==> !(x || !x))] //~ ERROR postcondition might not hold
fn foo9(x: bool) {}

// The exact error position reported in some of the cases below depends on AST
// optimisations performed within Silver; in particular, the `x == x` part is
// no longer optimised to `true` (since Silver commit 86d3ab9). `foo14` below
// was added to make sure precise error positions can be reported in
// postconditions without depending on AST optimisations.

#[ensures(x == x)] //~ ERROR postcondition might not hold
#[ensures(false)]
fn foo10(x: bool) {}

#[ensures(false)] //~ ERROR postcondition might not hold
#[ensures(x == x)]
fn foo11(x: bool) {}

#[ensures(x == x)] //~ ERROR postcondition might not hold
#[ensures(!true)]
#[ensures(x == x)]
fn foo12(x: bool) {}

#[ensures(false)] //~ ERROR postcondition might not hold
#[ensures(result == x)]
pub fn foo13(x: u32) -> u32 {
    x
}

#[trusted] #[pure] fn unk1() -> bool { unimplemented!() }
#[trusted] #[pure] fn unk2() -> bool { unimplemented!() }
#[trusted] #[pure] fn unk3() -> bool { unimplemented!() }

#[requires(unk1())]
#[requires(unk3())]
#[ensures(unk1())]
#[ensures(unk2())] //~ ERROR postcondition might not hold
#[ensures(unk3())]
fn foo14() {}

fn main() {}
