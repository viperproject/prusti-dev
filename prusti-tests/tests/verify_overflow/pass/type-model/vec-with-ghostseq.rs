use prusti_contracts::*;

#[model]
struct Vec<#[generic] T: Copy+Clone+PartialEq> {
    ghost_seq: GhostSeq<T>,
}

#[trusted]
#[ensures(vec.model().ghost_seq.len() == 1 + old(vec.model().ghost_seq.len()))]
#[ensures(forall(|i: usize| 0 <= i && i < vec.model().ghost_seq.len() - 1 ==>
vec.model().ghost_seq.lookup(i) == old(vec.model().ghost_seq.lookup(i))
))]
#[ensures(vec.model().ghost_seq.lookup(old(vec.model().ghost_seq.len())) == val)]
fn vec_push(vec: &mut Vec<i32>, val: i32) {
    vec.push(val);
}

#[trusted]
#[ensures(result.model().ghost_seq.len() == 0)]
fn vec_create() -> Vec<i32> {
    Vec::new()
}

#[requires(0 <= i && i < vec.model().ghost_seq.len())]
#[requires(vec.model().ghost_seq.lookup(i) == val)]
#[trusted]
fn verify_ghost_lookup(vec: &Vec<i32>, i: usize, val: i32) {
}

#[requires(vec.model().ghost_seq.len() == len)]
#[trusted]
fn verify_ghost_len(vec: &Vec<i32>, len: usize) {
}

fn main() {
    let mut vec = vec_create();
    verify_ghost_len(&vec, 0);

    vec_push(&mut vec, 123);
    verify_ghost_len(&vec, 1);
    verify_ghost_lookup(&vec, 0, 123);

    vec_push(&mut vec, 456);
    verify_ghost_len(&vec, 2);
    verify_ghost_lookup(&vec, 0, 123);
    verify_ghost_lookup(&vec, 1, 456);
}

#[derive(Copy, Clone)]
struct GhostSeq<T: Clone + Copy + PartialEq> {
    phantom: std::marker::PhantomData<T>,
}

impl<T: Clone + Copy + PartialEq> GhostSeq<T> {
    #[pure]
    #[trusted]
    #[requires(0 <= i && i < self.len())]
    fn lookup(&self, i: usize) -> T {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    fn len(&self) -> usize {
        unimplemented!()
    }
}