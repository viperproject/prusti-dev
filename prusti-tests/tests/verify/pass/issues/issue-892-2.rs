use prusti_contracts::*;

#[trusted]
#[ensures(match result {
    Ok(Some(r)) => r < 100,
    _ => true,
})]
pub fn foo() -> Result<Option<usize>, ()> {
    Ok(None)
}

fn main() {
    let _ = foo();
}
