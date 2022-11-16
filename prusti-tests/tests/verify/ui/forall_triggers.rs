use prusti_contracts::*;

#[pure]
fn count(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        count(n-1) + 1
    }
}

#[requires(forall(|n: usize, res: usize| count(n) == res ==> true, triggers=[(count(n),)]))]
pub fn test1() {}

#[requires(forall(|n: usize, res: usize| count(n) == res ==> true, triggers=[(if res == 5 {count(n)} else {3},)]))]
pub fn test2() {}

#[requires(forall(|n: usize, res: usize| count(n) == res ==> true, triggers=[(res == count(n),)]))]
pub fn test3() {}

fn main() {}
