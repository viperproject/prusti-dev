use prusti_contracts::*;

#[extern_spec]
impl<T: std::cmp::PartialEq> std::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;
}

// cloned unwrap
#[trusted]
#[pure]
#[requires(opt.is_some())]
#[ensures(match opt {
    Some(value) => *value == result,
    None => unreachable!(),
})]
fn option_peek(opt: &Option<usize>) -> usize { unimplemented!() }

fn main() {}

predicate! {
    fn sorted(s: &[i32]) -> bool {
        forall(|i: usize, j: usize| (i < j && j < s.len()) ==> s[i] <= s[j])
    }
}

#[requires(sorted(s))]
#[ensures(result.is_some() ==> option_peek(&result) < s.len() && s[option_peek(&result)] == n)]
#[ensures(result.is_none() ==> forall(|i: usize| (i < s.len() ==> s[i] != n)))]
pub fn binary_search(s: &[i32], n: i32) -> Option<usize> {
    let mut base = 0;
    let mut size = s.len();

    let mut result = None;

    while size > 0 {
        body_invariant!(base + size <= s.len());
        body_invariant!(size > 0 && result.is_none());
        body_invariant!(n == old(n));
        body_invariant!(sorted(s));
        body_invariant!(forall(|k: usize| (k < base) ==> s[k] < n));
        body_invariant!(result.is_none() ==>
            forall(|k: usize| (base + size <= k && k < s.len()) ==> n < s[k])
        );
        body_invariant!(result.is_some() ==>
            option_peek(&result) < s.len() && s[option_peek(&result)] == n);

        let half = size / 2;
        let mid = base + half;

        if s[mid] > n {
            size -= half;
        } else if s[mid] < n {
            base = mid;
            size -= half;
        } else {
            result = Some(mid);
            size = 0; // break
        }
    }

    result
}
