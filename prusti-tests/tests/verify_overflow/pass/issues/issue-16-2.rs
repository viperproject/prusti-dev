use prusti_contracts::*;

// A trait that says every member of a type can be assigned an integer value.
pub trait Val {
    #[pure]
    //#[trusted]
    fn value(&self) -> i32;
}

pub struct VecWrapper<T> {
    v: Vec<T>,
}

// Vector of objects that support the `Val` trait above
impl<T> VecWrapper<T>
where
    T: Val,
{
    #[trusted]
    #[pure]
    #[ensures(result < (isize::MAX as usize))]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn value(&self, index: usize) -> i32 {
        self.v[index].value()
    }
}

pub enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            UsizeOption::Some(_) => false,
            UsizeOption::None => true,
        }
    }
}

/// This implements binary search for any type that implements `Val` above.
/// The result will be an element of the array that maps to the same value.
/// Comparisons between two elements `x` and `y` are done by comparing
/// `x.value()` and `y.value()`.
#[requires(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==> arr.value(k1) <= arr.value(k2)))]
#[ensures(result.is_none() ==>
    (forall(|k: usize| (0 <= k && k < arr.len()) ==> arr.value(k) != elem.value())))]
#[ensures(match result {
    UsizeOption::Some(index) => (
        0 <= index && index < arr.len() && arr.value(index) == elem.value()
    ),
    UsizeOption::None => true,
})]
fn binary_search<T: Val>(arr: &VecWrapper<T>, elem: &T) -> UsizeOption {
    let mut size = arr.len();
    let mut base = 0usize;

    let mut result = UsizeOption::None;
    let mut continue_loop = size > 0;

    while continue_loop {
        body_invariant!(continue_loop == (size > 0 && result.is_none()));
        body_invariant!(base + size <= arr.len());
        body_invariant!(
            forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==> arr.value(k1) <= arr.value(k2))
        );
        body_invariant!(
            forall(|k: usize| (0 <= k && k < base) ==> arr.value(k) < elem.value())
        );
        body_invariant!(
            result.is_none() ==>
                (forall(|k: usize| (base + size <= k && k < arr.len()) ==> elem.value() != arr.value(k)))
        );
        body_invariant!(match result {
            UsizeOption::Some(index) => (
                0 <= index && index < arr.len() && arr.value(index) == elem.value()
            ),
            UsizeOption::None => true,
        });

        let half = size / 2usize;
        let mid = base + half;

        let mid_element = arr.value(mid);
        base = if mid_element < elem.value() {
            mid
        } else if mid_element > elem.value() {
            base
        } else {
            result = UsizeOption::Some(mid);
            base // Just return anything because we are finished.
        };

        size -= half;
        continue_loop = size > 0 && result.is_none();
    }

    result
}

/// Variant of the above. Most of the loop invariants are not needed, because
/// if a value is returned (using `result = Some(..)` in the original), then
/// the loop is exited immediately and only the postcondition needs to be shown.
/// The third postcondition, matching a `Some(..)` result does not actually
/// require that all the elemnets before the given index are less than `elem`,
/// which is what the fourth loop invariant would be needed for. Finally, the
/// third invariant should be framed, because `arr` is not modified in the loop.
#[requires(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==> arr.value(k1) <= arr.value(k2)))]
#[ensures(result.is_none() ==>
    (forall(|k: usize| (0 <= k && k < arr.len()) ==> arr.value(k) != elem.value())))]
#[ensures(match result {
    UsizeOption::Some(index) => (
        0 <= index && index < arr.len() && arr.value(index) == elem.value()
    ),
    UsizeOption::None => true,
})]
fn binary_search_alt<T: Val>(arr: &VecWrapper<T>, elem: &T) -> UsizeOption {
    let mut size = arr.len();
    let mut base = 0usize;

    while size > 0 {
        body_invariant!(base + size <= arr.len());

        let half = size / 2usize;
        let mid = base + half;

        let mid_element = arr.value(mid);
        base = if mid_element < elem.value() {
            mid
        } else if mid_element > elem.value() {
            base
        } else {
            return UsizeOption::Some(mid);
        };

        size -= half;
    }

    UsizeOption::None
}

#[trusted]
fn main() {}
