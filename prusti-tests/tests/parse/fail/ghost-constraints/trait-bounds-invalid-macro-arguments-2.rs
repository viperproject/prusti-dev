use prusti_contracts::*;

#[refine_spec(where 42 [ //~ ERROR: expected one of: `for`, parentheses, `fn`, `unsafe`, `extern`, identifier, `::`, `<`, square brackets, `*`, `&`, `!`, `impl`, `_`, lifetime
    ensures(result > 0)
])]
//~| ERROR: expected a trait bound and specifications in brackets, e.g.: `ghost_constraint(T: A + B + ..., [requires(...), ...])`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
