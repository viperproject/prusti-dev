extern crate prusti_contracts;
extern crate prusti_contracts_common;
extern crate library_contracts_lib;
extern crate library_contracts_extern_specs;

use library_contracts_lib::Opt;

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
    // The following extern spec block is not needed:
    /*
    #[extern_spec]
    impl<T> Option<T> {
        #[ensures(matches!(*self, Some(_)) == result)]
        fn is_some(&self) -> bool;
    }
    */

    let c = Some(42);
    let d = None::<i32>;
    assert!(c.is_some() == true);
    assert!(d.is_some() == false);
}
