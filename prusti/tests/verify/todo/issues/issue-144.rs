//! Source: crate `ena`

extern crate prusti_contracts;

struct UnificationTable;

impl<'tcx> UnificationTable {
    #[trusted]
    fn unify_var_var(&mut self) {
        unimplemented!()
    }

    fn union(&mut self) {
        self.unify_var_var();
    }
}

#[trusted]
fn main() {}
