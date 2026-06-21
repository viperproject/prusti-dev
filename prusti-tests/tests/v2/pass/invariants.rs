use prusti_contracts::*;

#[trusted]
fn main() {}

/// Arbitrary value to drive a loop condition.
#[trusted]
fn choose() -> bool { true }

/// Even without a body invariant, we should frame information about variables
/// that are not modified within the body of a loop. Here, `j` is initialised
/// to a constant value before the loop, so the *assertion* that `j == 43`
/// should pass for every iteration.
// TODO: base this on PCG information re: read/write places in a loop; for
//   places that are read-only, use half a permission in the permission part of
//   the loop invariant
fn test_loop_framing() {
    let j = 43;
    while choose() {
        body_invariant!(j == 43); // TODO: this should not be needed!
        assert!(j == 43);
    }
}

/// To make sure the edge case of an empty loop works.
fn test_infinte_empty() {
    loop {}
}

/// Same as `test_infinite_empty`, with a trivial loop invariant.
fn test_infinite_loop_invariant() {
    loop { body_invariant!(true); }
}

/// Basic use case for a loop invariant: enforce range of values on the
/// iteration variable. Be able to prove that the variable has reached a
/// specific value from the negation of the loop condition and a previously
/// assumed loop invariant.
fn test_basic() {
    let mut x = 0;
    loop {
        if x >= 10 {
            break;
        }
        body_invariant!(x < 10);
        x += 1;
    }
    assert!(x == 10);
}

/// Same as `test_basic` but using `while` loop syntax.
fn test_basic_while() {
    let mut x = 0;
    while x < 10 {
        body_invariant!(x < 10);
        x += 1;
    }
    assert!(x == 10);
}

/// Multiple invariant annotations should be supported.
fn test_multiple_invariants() {
    let x = 42;
    let y = 72;
    loop {
        body_invariant!(y == 72);
        body_invariant!(x == 42);
    }
}

/// If there are multiple body invariants, they should all be in the same place.
// TODO: this should not be accepted and probably produces incorrect Viper code
fn test_multiple_invariants_wrong() {
    let x = 42;
    let y = 72;
    loop {
        body_invariant!(y == 72);
        choose();
        body_invariant!(x == 42);
        choose();
    }
}
/*
/// Pathological case described in `mir_impure.rs` -- a loop with a body
/// invariant in the loop guard of a loop with a body invariant. This should
/// result in duplication of multiple basic blocks.
// TODO: still produces an irreducible CFG -- maybe the `break;` in (IN) does
//   not jump to where it is supposed to?
fn test_pathological_nesting() {
    while { // (OUT)
        loop { // (IN)
            if choose() {
                break;
            }
            body_invariant!(true);
            choose();
        }
        choose()
    } {
        choose();
        body_invariant!(false);
        choose();
    }
}
*/
/// The loop invariant should be able to refer to a local variable declared
/// within the loop.
// TODO: the issue here is where to emit the body invariant exactly: the CFG
//   we get Prusti side places the invariant basic blocks after the `let`
//   statement as expected, but we need to emit it as part of the label of a
//   basic block that is actually reached -- here we could move it to the succ
//   of the block that contains the `i` declaration, but what if there are
//   multiple successors? (or is it guaranteed by our encoding that there will
//   not be?)
fn test_invariant_following_local_decl() {
    while choose() {
        let mut i = 42;
        choose(); // TODO: this should not be needed!
        body_invariant!(i == 42);
        i += 1;
        assert!(i > 42);
    }
}
