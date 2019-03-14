//! Source: crate `ena`

extern crate prusti_contracts;

struct UnificationTable;

impl<'tcx> UnificationTable {
    #[trusted]
    fn unify_var_var(&mut self) {
        unimplemented!()
    }
}

fn union(orig_this: UnificationTable) {
    let mut this = orig_this;
    this.unify_var_var();
}

#[trusted]
fn main() {}
