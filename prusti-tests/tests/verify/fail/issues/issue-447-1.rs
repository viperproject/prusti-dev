use prusti_contracts::*;

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max_usize(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
    }
}

#[pure]
#[trusted]
fn slice_len<T>(slice: &[T]) -> usize {
    slice.len()
}

#[pure]
#[trusted]
fn vec_len<T>(vec: &Vec<T>) -> usize {
    vec.len()
}

#[trusted]
#[ensures(vec_len(vec) == old(vec_len(vec)) + 1)]
fn push<T>(vec: &mut Vec<T>, value: T) {
    vec.push(value)
}

#[trusted]
#[requires(ix < slice_len(slice))]
fn index_slice<T>(slice: &[T], ix: usize) -> &T {
    &slice[ix]
}

fn push_all<T: Clone>(vec: &mut Vec<T>, slice: &[T]) {
    for i in 0..slice_len(slice) { //~ ERROR iterators are not fully supported
        push(vec, index_slice(slice, i).clone())
    }
}

fn main(){}
