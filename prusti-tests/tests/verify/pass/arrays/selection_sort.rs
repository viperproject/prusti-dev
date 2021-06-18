use prusti_contracts::*;

fn main() {}


fn selection_sort(mut a: [i32; 10]) {
    let mut min;
    let mut i = 0;

    while i < a.len() {
        body_invariant!(0 <= i && i < 10);

        // sorted below i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                               ==> a[k1] <= a[k2]));
        // all below i are smaller than all above i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                               ==> a[k1] <= a[k2]));

        min = i;
        let mut j = i+1;
        while j < a.len() {
            // these three are the same as the outer loop
            body_invariant!(0 <= i && i < 10);
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                                   ==> a[k1] <= a[k2]));
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                                   ==> a[k1] <= a[k2]));

            // these are new
            body_invariant!(i < j && j < 10);
            body_invariant!(i <= min && min < 10);
            // all previously sorted are smaller than the current min
            body_invariant!(forall(|k: usize| (0 <= k && k < i) ==> a[k] <= a[min]));

            // all not-yet-sorted that we checked yet are bigger than the current min
            body_invariant!(forall(|k: usize| (i <= k && k < j && k < 10)
                                   ==> a[min] <= a[k]));

            if a[j] < a[min] {
                min = j;
            }

            j += 1;
        }

        let a_i = a[i];
        let a_min = a[min];
        a[i] = a_min;
        a[min] = a_i;

        i += 1;
    }
}
