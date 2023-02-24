// compile-flags: -Psif=true -Pserver_address=MOCK

// Example from "A Separation Logic for Enforcing Declarative Information Flow Control Policies"
// D. Costanzo and Z. Shao
// POST 2014

use prusti_contracts::*;

#[trusted]
#[requires(low(n))]
fn print(n: usize) {}

#[requires(forall(|i: usize| 0 <= i && i < schedule.len() ==> (schedule[i] == 0 ==> low(i))))]
fn print_availibility(schedule: &[u32]) {
    let mut i = 0;
    while i < schedule.len() {
        let x = schedule[i];
        if x == 0 {
            print(i);
        }
        i += 1;
    }
}

fn main() {}
