// `extern crate` is required to force the crate to be used
// otherwise Rust ignores it as it isn't used
extern crate library_contracts_extern_specs;
use library_contracts_lib::Opt;
use prusti_contracts::*;

// Demonstrating library contracts: specification is imported
// and thus corresponding #[extern_spec] blocks are not needed

fn main() {
    test_dependency_import();
    test_extern_specs();
    test_builtin_extern_specs();
}

fn test_dependency_import() {
    // Verifying contracts imported along with the functions.

    let a = Opt::Some(42);
    let b = Opt::None::<i32>;
    assert!(a.is_some() == true);
    assert!(b.is_some() == false);

    // Test that quantifiers are imported.
    library_contracts_lib::quantifier_test();
    prusti_assert!(library_contracts_lib::demo_fn(0));
    prusti_assert!(library_contracts_lib::quantifier_predicate(1));
}

fn test_extern_specs() {
    // Verifying imported extern specs

    let a = Opt::Some(42);
    let a_is_some = a.is_some();
    let b = a.map(|k| k > 0);
    assert!(a_is_some == b.is_some());
}

fn test_builtin_extern_specs() {
    // Verifying extern specs imported from `prusti_contracts`.
    let _ = divide(10).unwrap();
}

#[ensures((arg % 2 == 0) == result.is_ok())]
fn divide(arg: i32) -> Result<i32, ()> {
    if arg % 2 == 0 { Ok(arg/2) } else { Err(()) }
}
