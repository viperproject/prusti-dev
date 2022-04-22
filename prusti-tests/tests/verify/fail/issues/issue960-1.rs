use prusti_contracts::*;


#[requires(end <= slice.len())]
fn foo(slice: &[i32], start: usize, end: usize) {
    let subslice = &slice[start..end]; //~ ERROR the range end may be smaller than the start when slicing
}

#[requires(start <= end)]
fn bar(slice: &[i32], start: usize, end: usize) {
    let subslice = &slice[start..end]; //~ ERROR the range end value may be out of bounds when slicing
}

#[requires(end <= slice.len())]
fn foo_mut(slice: &mut [i32], start: usize, end: usize) {
    let subslice = &mut slice[start..end]; //~ ERROR mutably slicing is not fully supported yet
}

#[requires(start <= end)]
fn bar_mut(slice: &mut [i32], start: usize, end: usize) {
    let subslice = &mut slice[start..end]; //~ ERROR mutably slicing is not fully supported yet
}

fn main() {}