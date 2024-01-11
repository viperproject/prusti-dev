// compile-flags: -Puse_more_complete_exhale=false
use prusti_contracts::*;

/// A monotonically strictly increasing discrete function, with domain [0, domain_size)
pub trait Function {
    #[pure]
    fn domain_size(&self) -> usize;

    #[pure]
    #[requires(x < self.domain_size())]
    fn eval(&self, x: usize) -> i32;

    predicate!{
        fn invariant(&self) -> bool {
            forall(|x1: usize, x2: usize|
                x1 < x2 && x2 < self.domain_size() ==> self.eval(x1) < self.eval(x2)
            )
        }
    }
}

/// Find the unique `x` s.t. `f(x) == target`
#[requires(f.invariant())]
#[ensures(match result {
    Some(found_x) => {
        f.eval(found_x) == target &&
        forall(|x: usize| x < f.domain_size() && f.eval(x) == target ==> x == found_x)
    }
    None => {
        forall(|x: usize| x < f.domain_size() ==> f.eval(x) != target)
    }
})]
pub fn bisect<T: Function>(f: &T, target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = f.domain_size();
    while low < high {
        body_invariant!(high <= f.domain_size());
        body_invariant!(forall(|x: usize|
            (x < low || high <= x) && x < f.domain_size() ==> f.eval(x) != target
        ));
        let mid = low + ((high - low) / 2);
        let mid_val = f.eval(mid);
        if mid_val < target {
            low = mid + 1;
        } else if mid_val > target {
            high = mid;
        } else {
            return Some(mid)
        }
    }
    None
}

fn main() {}
