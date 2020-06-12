//! An adaptation of the example from
//! https://rosettacode.org/wiki/Knapsack_problem/0-1#Rust
//!
//! Changes:
//!
//! +   Replaced the type of the `name` field from `&'static str` to `usize`.
//! +   Wrapped built-in types and functions.
//! +   Add additional functions and fields for capturing functional specification.
//! +   Change the loop into the supported shape.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   The implementation computes the values of the function `m` given in
//!     https://en.wikipedia.org/wiki/Knapsack_problem#0/1_knapsack_problem
//! +   We could not express the postcondition that the result is
//!     correct because that requires support for comprehensions.

extern crate prusti_contracts;

pub struct Item {
    name: usize,
    weight: usize,
    value: usize
}

pub struct Items{
    v: Vec<Item>,
}

impl Items {
    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="result > 0"]
    pub fn lookup_weight(&self, index: usize) -> usize {
        self.v[index].weight
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="result >= 0"]
    pub fn lookup_value(&self, index: usize) -> usize {
        self.v[index].value
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.lookup_weight(index) == result.weight"]
    #[ensures="self.lookup_value(index) == result.value"]
    pub fn index(&self, index: usize) -> &Item {
        &self.v[index]
    }
}

pub struct ItemIndices{
    v: Vec<usize>,
}

impl ItemIndices {

    #[trusted]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Vec::with_capacity(capacity),
        }
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    pub fn push(&mut self, value: usize) {
        self.v.push(value);
    }
}

pub struct BestValues {
    _ghost_item_len: usize,
    _ghost_weight_len: usize,
    v: Vec<Vec<usize>>,
}

impl BestValues {

    #[trusted]
    #[ensures="result.item_len() == item_len"]
    #[ensures="result.weight_len() == weight_len"]
    #[ensures="forall ii: usize, wi: usize ::
                    (0 <= ii && ii < result.item_len() && 0 <= wi && wi < result.weight_len()) ==>
                    result.lookup(ii, wi) == default"]
    pub fn new(default: usize, weight_len: usize, item_len: usize) -> Self {
        Self {
            _ghost_item_len: item_len,
            _ghost_weight_len: weight_len,
            v: vec![vec![default; weight_len]; item_len],
        }
    }

    #[pure]
    pub fn item_len(&self) -> usize {
        self._ghost_item_len
    }

    #[pure]
    pub fn weight_len(&self) -> usize {
        self._ghost_weight_len
    }

    #[trusted]
    #[pure]
    #[requires="0 <= item_index && item_index < self.item_len()"]
    #[requires="0 <= weight_index && weight_index < self.weight_len()"]
    pub fn lookup(&self, item_index: usize, weight_index: usize) -> usize {
        self.v[item_index][weight_index]
    }

    #[trusted]
    #[requires="0 <= item_index && item_index < self.item_len()"]
    #[requires="0 <= weight_index && weight_index < self.weight_len()"]
    #[ensures="self.lookup(item_index, weight_index) == *result"]
    pub fn index(&self, item_index: usize, weight_index: usize) -> &usize {
        &self.v[item_index][weight_index]
    }

    #[trusted]
    #[requires="0 <= item_index && item_index < self.item_len()"]
    #[requires="0 <= weight_index && weight_index < self.weight_len()"]
    #[ensures="after_expiry(
        self.item_len() == old(self.item_len()) &&
        self.weight_len() == old(self.weight_len()) &&
        self.lookup(item_index, weight_index) == before_expiry(*result) &&
        (forall ii: usize, wi: usize ::
            (0 <= ii && ii < self.item_len() &&
             0 <= wi && wi < self.weight_len() &&
             !(ii == item_index && wi == weight_index)) ==>
            self.lookup(ii, wi) == old(self.lookup(ii, wi)))
        )"]
    pub fn index_mut(&mut self, item_index: usize, weight_index: usize) -> &mut usize {
        &mut self.v[item_index][weight_index]
    }
}

#[pure]
fn max(a: usize, b: usize) -> usize {
    if a < b {
        b
    } else {
        a
    }
}

/// Check that values stored in ``best_value`` correspond to the function ``m`` from
/// https://en.wikipedia.org/wiki/Knapsack_problem#0/1_knapsack_problem
///
/// *   $m[0,\,w]=0$
/// *   $m[i,\,w]=m[i-1,\,w]$ if $w_i > w\,\!$ (the new item is more than the current weight limit)
/// *   $m[i,\,w]=\max(m[i-1,\,w],\,m[i-1,w-w_i]+v_i)$ if $w_i \leqslant w$.
#[pure]
#[requires="0 <= i && i <= items.len()"]
#[requires="0 <= w && w <= max_weight"]
fn m(items: &Items, i: usize, w: usize, max_weight: usize) -> usize {
    match (i, w) {
        (0, _w) => 0,
        (i, w) => {
            if items.lookup_weight(i-1) > w {
                m(items, i-1, w, max_weight)
            } else {
                max(m(items, i-1, w, max_weight),
                    m(items, i-1, w-items.lookup_weight(i-1), max_weight) + items.lookup_value(i-1))
            }
        }
    }
}

#[requires="items.len() < std::usize::MAX"]
#[requires="2 <= max_weight && max_weight < std::usize::MAX"]
pub fn knapsack01_dyn(items: &Items, max_weight: usize) -> ItemIndices {
    let mut best_value = BestValues::new(0, max_weight + 1, items.len() + 1);
    let mut i = 0;
    let mut continue_loop_1 = i < items.len();
    #[invariant="items.len() + 1 == best_value.item_len()"]
    #[invariant="max_weight + 1 == best_value.weight_len()"]
    #[invariant="i < items.len()"]
    #[invariant="0 <= i && i < items.len()"]
    #[invariant="2 <= max_weight && max_weight < std::usize::MAX"]
    #[invariant="forall ii: usize, wi: usize ::
                    (0 <= ii && ii < best_value.item_len() && 0 <= wi && wi < best_value.weight_len()) ==>
                    best_value.lookup(ii, wi) >= 0"]
    #[invariant="forall ii: usize ::
                    (0 <= ii && ii < best_value.item_len()) ==>
                    best_value.lookup(ii, 0) == 0"]
    #[invariant="forall ii: usize, wi: usize ::
                    (0 <= ii && ii <= i && 0 <= wi && wi < best_value.weight_len()) ==>
                    m(items, ii, wi, max_weight) == best_value.lookup(ii, wi)"]
    while continue_loop_1 {
        let it = items.index(i);

        let mut w = 1;
        #[invariant="w <= max_weight"]
        #[invariant="items.len() + 1 == best_value.item_len()"]
        #[invariant="max_weight + 1 == best_value.weight_len()"]
        #[invariant="0 <= w && w <= best_value.weight_len()"]
        #[invariant="0 <= i && i < items.len()"]
        #[invariant="2 <= max_weight && max_weight < std::usize::MAX"]
        #[invariant="it.value == items.lookup_value(i)"]
        #[invariant="it.weight == items.lookup_weight(i)"]
        #[invariant="forall ii: usize, wi: usize ::
                        (0 <= ii && ii < best_value.item_len() && 0 <= wi && wi < best_value.weight_len()) ==>
                        best_value.lookup(ii, wi) >= 0"]
        #[invariant="forall ii: usize, wi: usize ::
                        (0 <= ii && ii <= i && 0 <= wi && wi < best_value.weight_len()) ==>
                        m(items, ii, wi, max_weight) == best_value.lookup(ii, wi)"]
        #[invariant="forall wi: usize :: (0 <= wi && wi < w) ==>
                        m(items, i+1, wi, max_weight) == best_value.lookup(i+1, wi)"]
        #[invariant="forall ii: usize ::
                        (0 <= ii && ii < best_value.item_len()) ==>
                        best_value.lookup(ii, 0) == 0"]
        while w <= max_weight {
            let new_best_value = if it.weight > w {
                *best_value.index(i, w)
            } else {
                max(*best_value.index(i, w),
                    *best_value.index(i, w - it.weight) + it.value)
            };
            let val = best_value.index_mut(i+1, w);
            *val = new_best_value;
            w += 1;
        }

        i += 1;
        continue_loop_1 = i < items.len();
    }
 
    let mut result = ItemIndices::with_capacity(items.len());
    let mut left_weight = max_weight;
 
    let mut i = items.len();
    #[invariant="0 < i && i <= items.len()"]
    #[invariant="items.len() + 1 == best_value.item_len()"]
    #[invariant="max_weight + 1 == best_value.weight_len()"]
    #[invariant="0 <= left_weight && left_weight <= max_weight"]
    #[invariant="forall ii: usize, wi: usize ::
                    (0 <= ii && ii < best_value.item_len() && 0 <= wi && wi < best_value.weight_len()) ==>
                    m(items, ii, wi, max_weight) == best_value.lookup(ii, wi)"]
    while 0 < i {
        i -= 1;
        let it = items.index(i);
        if *best_value.index(i+1, left_weight) != *best_value.index(i, left_weight) {
            result.push(i);
            left_weight -= it.weight;
        }
    }
 
    result
}

fn main() {}
