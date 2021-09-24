use prusti_contracts::*;

fn main() {
    let x = [1, 3, 5];
    let y = [2, 4, 6];
    let m = merge(x, y);
    assert!(m[1] <= m[4]);
}


predicate! {
    fn sorted3(a: &[i32; 3]) -> bool {
        forall(|i: usize, j: usize| (0 <= i && i < j && j < 3) ==> a[i] <= a[j])
    }
}

predicate! {
    fn sorted6(a: &[i32; 6]) -> bool {
        forall(|i: usize, j: usize| (0 <= i && i < j && j < 6) ==> a[i] <= a[j])
    }
}


#[requires(sorted3(&a) && sorted3(&b))]
#[ensures(sorted6(&result))]
fn merge(a: [i32; 3], b: [i32; 3]) -> [i32; 6] {
    let mut a_pos = 0;
    let mut b_pos = 0;
    let mut res_pos = 0;

    let mut res = [0; 6];

    while res_pos < res.len() {
        // indices
        body_invariant!(0 <= a_pos && a_pos <= 3);
        body_invariant!(0 <= b_pos && b_pos <= 3);
        body_invariant!(0 <= res_pos && res_pos < 6);
        body_invariant!(a_pos + b_pos == res_pos);

        // subsequences and partial result sorted
        body_invariant!(sorted3(&a));
        body_invariant!(sorted3(&b));
        body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < j && j < res_pos) ==> res[i] <= res[j]));

        // all already sorted are smaller than remaining in a, b
        body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < res_pos && a_pos <= j && j < 3) ==> res[i] <= a[j]));
        body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < res_pos && b_pos <= j && j < 3) ==> res[i] <= b[j]));

        body_invariant!(res_pos > 0 && a_pos < 3 ==> res[res_pos - 1] <= a[a_pos]);
        body_invariant!(res_pos > 0 && b_pos < 3 ==> res[res_pos - 1] <= b[b_pos]);

        if b_pos == 3 || a_pos < 3 && a[a_pos] <= b[b_pos] {
            res[res_pos] = a[a_pos];
            a_pos += 1;
        } else {
            res[res_pos] = b[b_pos];
            b_pos += 1;
        }
        res_pos += 1;
    }

    assert!(res_pos == res.len());

    res
}
