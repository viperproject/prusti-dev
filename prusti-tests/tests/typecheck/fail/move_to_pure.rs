// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

struct UnexpectedValue(u32);

#[pure]
fn is_ok<T>(x: Result<T, UnexpectedValue>) -> bool {
    if let Ok(_) = x {
        true
    } else {
        false
    }
}

#[pure]
#[requires(is_ok(x))]
fn get_ok_bool(x: Result<bool, UnexpectedValue>) -> bool {
    if let Ok(v) = x {
        v
    } else {
        unreachable!()
    }
}

#[ensures(is_ok(result) && get_ok_bool(result))] //~ ERROR use of moved value
fn test(i: u32) -> Result<bool, UnexpectedValue> {
    Ok(true)
}

fn main() {}
