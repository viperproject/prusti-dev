use prusti_contracts::*;

#[requires(a === b)]
fn foo<T>(a: T, b: T) {}

struct X { a: i32 }

fn main() {
    foo(5, 5);
    foo(true, true);
    foo((1, 2), (1, 2));
    foo(X { a: 1 }, X { a: 1 });
}
