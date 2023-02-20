use prusti_contracts::*;

#[refine_spec(where 42, [ //~ ERROR: expected one of: `for`, parentheses, `fn`, `unsafe`, `extern`, identifier, `::`, `<`, square brackets, `*`, `&`, `!`, `impl`, `_`, lifetime
    ensures(result > 0)
])]
//~| ERROR: expected where constraint and specifications in brackets, e.g.: `refine_spec(where T: A + B, U: C, [requires(...), ...])`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
