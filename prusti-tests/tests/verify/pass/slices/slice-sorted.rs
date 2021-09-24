use prusti_contracts::*;

fn main() {}


predicate! {
    fn sorted(s: &[i32]) -> bool {
        forall(|i: usize, j: usize| (0 <= i && i < j && j < s.len()) ==> s[i] <= s[j])
    }
}

#[requires(sorted(s))]
fn requires_sorted(s: &[i32]) {
    if s.len() > 3 {
        assert!(s[0] <= s[3]);
    }
}

/*
#[requires(sorted(s) && s.len() > 2)]
fn slice_sorted(s: &[i32]) {
    let ss = &s[..2];
    assert!(ss[0] <= ss[1]);
}

#[requires(sorted(&a[0..2]))]
fn requires_sorted_start(a: [i32; 3]) {
    assert!(a[0] <= a[1]);
}
*/
