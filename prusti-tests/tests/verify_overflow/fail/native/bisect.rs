use prusti_contracts::*;

/// A monotonically increasing discrete function, with domain [0, domain_size)
struct Function;

impl Function {
    #[pure]
    #[trusted] // abstract, actual implementation doesn't matter
    fn domain_size(&self) -> usize {
        42
    }

    #[pure]
    #[trusted]
    #[requires(x < self.domain_size())]
    fn eval(&self, x: usize) -> i32 {
        x as i32
    }
}

/// Find the `x` s.t. `f(x) == target`
#[ensures(if let Some(x) = result { f.eval(x) == target } else { true })]
fn bisect(f: &Function, target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = f.domain_size();
    assert!(high == f.domain_size());
    while low < high {
        body_invariant!(low < high && high <= f.domain_size());
        let mid = (low + high) / 2; //~ ERROR attempt to add with overflow
        let mid_val = f.eval(mid);
        if mid_val < target {
            low = mid + 1;
        } else if mid_val > target {
            high = mid;
        } else {
            return Some(mid);
        }
    }
    None
}

fn main() {}
