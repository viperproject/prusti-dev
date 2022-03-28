extern crate prusti_contracts;
use prusti_contracts::*;

/// External traits
trait RestrictiveTrait {
    fn foo(&self, x: i32) -> i32;
}
/// External traits

#[extern_spec]
trait RestrictiveTrait {
    #[requires(x > 10)]
    fn foo(&self, x: i32) -> i32;
}

struct PermissiveImpl;

#[refine_trait_spec]
impl RestrictiveTrait for PermissiveImpl {
    #[requires(_x != 0)]
    fn foo(&self, _x: i32) -> i32 {
        42
    }
}

struct RestrictiveImpl;
impl RestrictiveTrait for RestrictiveImpl {
    fn foo(&self, _x: i32) -> i32 {
        42
    }
}

fn main() {
    let permissive_impl = PermissiveImpl { };
    permissive_impl.foo(15);
    RestrictiveTrait::foo(&permissive_impl, 15);
    permissive_impl.foo(5);
    RestrictiveTrait::foo(&permissive_impl, 5);

    let restrictive_impl = RestrictiveImpl { };
    restrictive_impl.foo(15);
    RestrictiveTrait::foo(&restrictive_impl, 15);
}