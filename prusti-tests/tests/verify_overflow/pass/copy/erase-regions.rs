use prusti_contracts::*;
use std::slice::Iter;

#[model]
struct Iter<'a, #[generic] T: Copy> {
    position: usize,
}

type SliceTy<T> = [T];
#[extern_spec]
impl<T: Copy+PartialEq> SliceTy<T> {
    #[pure]
    fn len(&self) -> usize;

    #[ensures( result.model().position == 0 )]
    fn iter(&self) -> std::slice::Iter<'_, T>;
}

fn verify_slice_iter(slice: &[i32]) {
    let iter = slice.iter();
}

fn main() {

}