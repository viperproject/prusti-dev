use prusti_contracts::*;


fn main() {}

predicate! {
    fn sorted(s: &[i32]) -> bool {
        forall(|i: usize, j: usize| (0 <= i && i < j && j < s.len()) ==> s[i] <= s[j])
    }
}

enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    fn is_none(&self) -> bool {
        !self.is_some()
    }
    #[pure]
    #[requires(self.is_some())]
    fn peek(&self) -> usize {
        match self {
            UsizeOption::Some(n) => *n,
            UsizeOption::None => unreachable!(),
        }
    }
}


#[requires(sorted(s))]
#[requires(s.len() < 18446744073709551615)] // usize limits
#[ensures(result.is_some() ==> 0 <= result.peek() && result.peek() < s.len() && s[result.peek()] == n)]
#[ensures(result.is_none() ==> forall(|i: usize| (0 <= i && i < s.len() ==> s[i] != n)))]
fn binary_search(s: &[i32], n: i32) -> UsizeOption {
    let mut base = 0;
    let mut size = s.len();

    let mut result = UsizeOption::None;

    // TODO: do we have proper value preservation in slices?
    while size > 0 {
        body_invariant!(base + size <= s.len());
        body_invariant!(size > 0 && result.is_none());
        body_invariant!(n == old(n));
        body_invariant!(sorted(s));
        body_invariant!(forall(|k: usize| (0 <= k && k < base) ==> s[k] < n));
        body_invariant!(result.is_none() ==>
             forall(|k: usize| (base + size <= k && k < s.len()) ==> n < s[k])
        );
        body_invariant!(result.is_some() ==> (
                0 <= result.peek() && result.peek() < s.len() && s[result.peek()] == n));

        let half = size / 2;
        let mid = base + half;

        if s[mid] > n {
            size -= half;
        } else if s[mid] < n {
            base = mid;
            size -= half;
        } else {
            assert!(s[mid] == n);
            result = UsizeOption::Some(mid);
            size = 0; // break
        }
    }

    return result;
}
