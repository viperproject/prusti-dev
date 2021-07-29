use prusti_contracts::*;
use export_specs_crate;

prusti_use!(export_specs_crate::std::option::Option);
fn main() {
    let mut x = Some(3);
    assert!(x.is_some());
    x = None;
    assert!(x.is_none());
}
