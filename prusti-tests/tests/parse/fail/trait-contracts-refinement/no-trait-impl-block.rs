use prusti_contracts::*;

struct Foo;

#[refine_trait_spec]
impl Foo { //~ ERROR: Can refine trait specifications only on trait implementation blocks
    fn foo(&self) {
    }
}

fn main() {
}