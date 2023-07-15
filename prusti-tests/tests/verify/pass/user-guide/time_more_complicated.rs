// compile-flags: -Ptime_reasoning=true
//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

#[requires(time_credits(1))]
fn main() {}

//// ANCHOR: code
#[requires(if more_work { time_credits(11) } else { time_credits(6) })]
fn do_work(more_work: bool) {
    let mut i = 0;
    while i < 5 {
        body_invariant!(time_credits(5 - i));
        i += 1;
    }
    if more_work {
        i = 0;
        while i < 5 {
            body_invariant!(time_credits(5 - i));
            i += 1;
        }
    }
}
//// ANCHOR_END: code
