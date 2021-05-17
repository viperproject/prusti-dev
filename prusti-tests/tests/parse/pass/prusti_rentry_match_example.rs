use prusti_contracts::*;

// ignore-test: prusti-expr! not yet implemented
#[ensures(
    match result {
        Ok(x) => prusti_expr!(forall(|i: usize| i < s.len() ==> is_digit(s[i]))) && int_to_string(x) == s,
        Err(_) => prusti_expr!(forall(|i: usize| i < s.len() ==> !is_digit(s[i])))
    }
)]
fn try_string_to_int(s: &str) -> Result<u32, <u32 as std::str::FromStr>::Err> {
    s.parse::<u32>()
}