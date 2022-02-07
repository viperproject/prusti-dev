// FIXME performance issue, see https://github.com/viperproject/prusti-dev/issues/819
// disabled `fix_quantifiers` and `optimize_folding` optimizations for now:
// compile-flags: -Poptimizations=inline_constant_functions,delete_unused_predicates,remove_empty_if,purify_vars,remove_unused_vars,remove_trivial_assertions,clean_cfg -Pverification_deadline=180

use prusti_contracts::*;

fn main() {}


#[ensures(forall(|k1: usize, k2: usize|(0 <= k1 && k1 < k2 && k2 < 10)
    ==> (get(a, k1) <= get(a, k2)),
    triggers=[(get(a, k1),get(a, k2),)]))]
fn selection_sort(a: &mut [i32; 10]) {
    let mut min;
    let mut i = 0;

    while i < a.len() {
        body_invariant!(0 <= i && i < 10);

        // sorted below i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                                ==> get(a, k1) <= get(a, k2),
                                triggers=[(get(a, k1),get(a, k2))]));
        // all below i are smaller than all above i
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                                ==> get(a, k1) <= get(a, k2),
                                triggers=[(get(a, k1),get(a, k2))]));

        min = i;
        let mut j = i+1;

        while j < a.len() {
            // these three are the same as the outer loop
            body_invariant!(0 <= i && i < 10);
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i)
                                    ==> get(a, k1) <= get(a, k2),
                                    triggers=[(get(a, k1),get(a, k2))]));
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < 10)
                                    ==> get(a, k1) <= get(a, k2),
                                    triggers=[(get(a, k1),get(a, k2))]));

            // these are new
            body_invariant!(i < j && j < 10);
            body_invariant!(i <= min && min < 10);
            // all previously sorted are smaller than the current min
            body_invariant!(forall(|k: usize| (0 <= k && k < i)
                                    ==> get(a, k) <= get(a, min),
                                    triggers=[(get(a, k))]));

            // all not-yet-sorted that we checked yet are bigger than the current min
            body_invariant!(forall(|k: usize| (i <= k && k < j && k < 10)
                                    ==> get(a, min) <= get(a, k),
                                    triggers=[(get(a, k))]));

            if get(a, j) < get(a, min) {
                min = j;
            }

            j += 1;
        }

        let a_i = get(a, i);
        let a_min = get(a, min);
        set(a, i,  a_min);
        set(a, min, a_i);

        i += 1;
    }
}

// FIXME: replace all instances of get/set with array indices when #812 is fixed https://github.com/viperproject/prusti-dev/issues/812

#[pure]
#[requires(0 <= i && i < 10)]
const fn get(a: &[i32; 10], i: usize) -> i32 {
    a[i]
}

#[requires(0 <= i && i < 10)]
#[ensures(forall(|j: usize| (0 <= j && j < 10 && j != old(i)) ==> (get(a, j) == old(get(a, j))), triggers=[(get(a, j),)]))]
#[ensures(get(a, old(i)) == old(v))]
fn set(a: &mut [i32; 10], i: usize, v: i32) {
    a[i] = v;
}
