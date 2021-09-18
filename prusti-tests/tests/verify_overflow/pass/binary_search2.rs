use prusti_contracts::*;

fn main() {}

predicate! {
    fn sorted(s: &[i32]) -> bool {
        forall(|i: usize, j: usize| (i < j && j < s.len()) ==> s[i] <= s[j])
    }
}

predicate! {
    fn contains_not(s: &[i32], start: usize, end: usize, n: i32) -> bool {
        forall(|i: usize| (start <= i && i < end) ==> s[i] != n)
    }
}

#[requires(sorted(s))]
#[ensures(
    match result {
        Some(index) => index < s.len() && s[index] == n,
        None => contains_not(s, 0, s.len(), n),
    }
)]
pub fn binary_search(s: &[i32], n: i32) -> Option<usize> {
    let mut base = 0;
    let mut size = s.len();

    let mut result = None;

    while size > 0 {
        body_invariant!(base + size <= s.len());
        body_invariant!(size > 0 && matches!(result, None));
        body_invariant!(n == old(n));
        body_invariant!(sorted(s));
        body_invariant!(forall(|k: usize| (k < base) ==> s[k] < n));
        body_invariant!(
            match result {
                Some(index) => index < s.len() && s[index] == n,
                None => contains_not(s, base + size, s.len(), n),
            }
        );

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
