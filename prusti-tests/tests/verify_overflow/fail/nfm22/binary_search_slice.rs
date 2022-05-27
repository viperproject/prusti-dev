use prusti_contracts::*;

#[requires(a.len() < usize::MAX / 2)]
#[ensures(if let Some(result) = result {
    a[result] == key
} else { true })]
fn search(a: &[i32], key: i32) -> Option<usize> {
  let mut low = 0;
  let mut high = a.len();
  while low < high {
    // Addition may overflow
    let mid = (low+high) / 2; //~ ERROR: attempt to add with overflow
    // Bound check at runtime
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

fn main() {}
