use prusti_contracts::*;

fn main() {}

#[extern_spec]
mod example {
    // parsing continues even after the first error
    use crate::*; //~ ERROR: `use` statements have no effect in #[extern_spec] modules; module contents share the outer scope.
    use crate::*; //~ ERROR: `use` statements have no effect in #[extern_spec] modules; module contents share the outer scope.

    #[pure]
    fn foo();
}

mod example {
    pub fn foo() {}
}
