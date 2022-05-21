// compile-flags: -Penable_type_invariants=true
use prusti_contracts::*;
fn main() {}

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

// fn sig with all types of invariant
fn foo(move_arg: Percentage, pure_arg: &Percentage, borrow_arg: &mut Percentage) -> Percentage {
    // Pres due to invariant
    // Seems that invariants aren't actually working in the current PR atm?
    assert!(move_arg.value <= 100);
    assert!(pure_arg.value <= 100);
    assert!(borrow_arg.value <= 100);

    // [Discussion 1]
    // Should invs be enforced across loops?
    // How to even do this with `body_invariant`?
    while borrow_arg.value < 42 {
        body_invariant!(borrow_arg.value < 100);
        borrow_arg.value += 1;
    }

    let result = move_arg;
    // Posts due to invariant
    assert!(borrow_arg.value <= 100);
    assert!(result.value <= 100);
    result
}
