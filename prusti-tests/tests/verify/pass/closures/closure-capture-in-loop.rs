// ignore-test: encodes without panicking, but verification fails with an
// unbacktranslatable `call.precondition:insufficient.permission` (same issue as
// other borrows that are live across a loop).

// The closure captures `c` by mutable reference, so the PCG sees a lifetime
// projection on the closure type, which has no regions in its decomposition.

pub fn map_with_counter() {
    let mut c = 0;
    for pair in [1, 2, 3].into_iter().map(|x| {
        c += 1;
        (x, c)
    }) {
        let _ = pair;
    }
}

fn main() {}
