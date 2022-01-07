extern crate prusti_contracts;
use prusti_contracts::*;

/// External traits
trait ExternTrait {
    fn foo(&self);
}
/// External traits

trait A {
    fn a(&self) -> bool;
}
trait B {
    fn b(&self) -> bool;
}
trait C {
    fn c(&self) -> bool;
}

#[extern_spec]
trait ExternTrait where Self: A + B, Self: C{
    #[requires(A::a(self) && self.b())]
    fn foo(&self);
}

struct S;

impl A for S{fn a(&self) -> bool {true}}
impl B for S{fn b(&self) -> bool {true}}
impl C for S{fn c(&self) -> bool {true}}

#[refine_trait_spec]
impl ExternTrait for S {
    #[requires(A::a(self) && self.b() && C::c(self))]
    fn foo(&self) {}
}

fn main() {}