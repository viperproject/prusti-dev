// FIXME performance issue, see https://github.com/viperproject/prusti-dev/issues/819
// disabled `fix_quantifiers` and `optimize_folding` optimizations for now:
// compile-flags: -Poptimizations=inline_constant_functions,delete_unused_predicates,remove_empty_if,purify_vars,remove_unused_vars,remove_trivial_assertions,clean_cfg -Pverification_deadline=180

use prusti_contracts::*;

fn main() {}


#[ensures(forall(|k1: usize, k2: usize|(0 <= k1 && k1 < k2 && k2 < 10)
    ==> (a[k1] <= a[k2]),
    triggers=[(a[k1],a[k2],)]))]
fn selection_sort(a: &mut [i32; 10]) {
    let mut min;
    let mut i = 0;

    while i < a.len() {
        body_invariant!(0 <= i && i < 10);

        // this body invariant is needed in order to trigger the correct quantifiers
        body_invariant!(a[0] <= a[i]);

        // sorted below i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                                ==> a[k1] <= a[k2],
                                triggers=[(a[k1],a[k2])]));
        // all below i are smaller than all above i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                                ==> a[k1] <= a[k2],
                                triggers=[(a[k1],a[k2])]));

        min = i;
        let mut j = i+1;

        while j < a.len() {
            // these three are the same as the outer loop
            body_invariant!(0 <= i && i < 10);
            body_invariant!(a[0] <= a[i]);
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                                    ==> a[k1] <= a[k2],
                                    triggers=[(a[k1],a[k2])]));
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                                    ==> a[k1] <= a[k2],
                                    triggers=[(a[k1],a[k2])]));

            // these are new
            body_invariant!(i < j && j < 10);
            body_invariant!(i <= min && min < 10);
            // all previously sorted are smaller than the current min
            body_invariant!(forall(|k: usize| (0 <= k && k < i)
                                    ==> a[k] <= a[min],
                                    triggers=[(a[k])]));

            // all not-yet-sorted that we checked yet are bigger than the current min
            body_invariant!(forall(|k: usize| (i <= k && k < j && k < 10)
                                    ==> a[min] <= a[k],
                                    triggers=[(a[k])]));

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
