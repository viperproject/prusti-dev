fn main() {}

fn slice_len_gt_0(x: &[i32]) {
    assert!(x.len() >= 0);
}

// this should generate a call to .len() for the bounds check and exercise the slice lookup pure
// function as well
fn slice_index(x: &[i32]) -> i32 {
    if x.len() > 3 {
        x[3]
    } else {
        -1
    }
}
