use prusti_contracts::*;

#[ensures(if let Some(result) = result {
    a[result] == key
} else { true })]
/// Counterexample postcond:
// #[ensures(if let Some(result) = result {
//     a[result] == key
// } else { false })]
fn search_fixed(a: &[i32], key: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = a.len();
    while low < high {
        // Note the addition of the loop guard to the loop invariant.
        // This would not be needed if PR #887 (or similar) was merged.
        body_invariant!(low < high && high <= a.len());
        let mid = low + ((high-low) / 2);
        assert!(mid < high);
        let mid_val = a[mid];
        if mid_val < key {
            low = mid + 1;
        } else if mid_val > key {
            high = mid;
        } else {
            return Some(mid);
        }
    }
    None
}

fn main() {
    let arr = [1, 2];
    let a = &arr[..];
    let idx = search_fixed(a, 1);
    if let Some(idx) = idx {
        // Postcond guarantees that
        // result is in bounds:
        assert!(idx < 2);
    }
}
