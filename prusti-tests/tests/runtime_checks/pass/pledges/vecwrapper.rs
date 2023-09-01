//@run
use prusti_contracts::*;

#[derive(Clone)]
pub struct VecWrapperI32 {
    pub v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    #[insert_runtime_check]
    #[ensures(result.len() == 5)]
    pub fn new() -> Self {
        Self {
            v: vec![1,2,3,4,5],
        }
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    /// A ghost function for specifying values stored in the vector.
    #[trusted]
    #[pure]
    #[insert_runtime_check]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    pub fn insert(&mut self, value: i32) {
        self.v.push(value);
    }

    #[trusted]
    #[insert_runtime_check]
    #[requires(index < self.len())]
    #[insert_runtime_check]
    #[ensures(*result == old(self.lookup(index)))]
    // failing pledge: the quantifier iterates over all elements
    // including the one that can be changed.
    #[insert_runtime_check]
    #[after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        forall(
            |i: usize| (i < self.len()) && i != index ==>
            self.lookup(i) == old(self.lookup(i))
        )
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }
}

fn main() {
    let mut vw = VecWrapperI32::new();
    let x = vw.index_mut(3);
    *x = 42;
    vw.insert(50)
}

