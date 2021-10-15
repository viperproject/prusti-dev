extern crate prusti_contracts;
use prusti_contracts::*;

// precondition inhale

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}


#[requires(percentage.value >= 10)]
fn adjust_percentage(percentage: &mut Percentage, flag: bool) { //~ ERROR type invariants
   let mut f0 = flag;
   if flag {
       percentage.value += 10; // temporarily break invariant
       f0 = false;
   } else {
       percentage.value = 120; // temporarily break invariant
       f0 = true
   }
   if f0 {
       percentage.value -= 10; // broken restore invariant
   } else {
       percentage.value -= 20; // broken restore invariant
   }
}

fn main() {}
