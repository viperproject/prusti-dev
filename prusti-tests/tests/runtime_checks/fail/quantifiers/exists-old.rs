//@run: 101
use prusti_contracts::*;

#[derive(Clone)]
struct VecWrapper {
    content: Vec<i32>,
}

impl VecWrapper {
    #[trusted]
    #[insert_runtime_check]
    #[ensures(result.len() == 8)]
    pub fn new() -> Self {
        Self {
            content: vec![1,2,3,4,5,6,7,8],
        }
    }

    #[pure]
    #[trusted]
    #[insert_runtime_check]
    #[requires(i < self.len())]
    pub fn lookup(&self, i: usize) -> i32 {
        *self.content.get(i).unwrap()
    }

    #[pure]
    #[trusted]
    pub fn len(&self) -> usize {
        self.content.len()
    }

    #[trusted]
    #[insert_runtime_check]
    #[requires(i < self.len())]
    #[insert_runtime_check]
    #[ensures(old(self.len()) == self.len())]
    // failing quantifier: all elements stay untouched
    #[insert_runtime_check]
    #[ensures(forall(|j: usize| (j < self.len()) ==> self.lookup(j) == old(self.lookup(j))))]
    pub fn set(&mut self, i: usize, x: i32) {
        self.content[i] = x;
    }
}

#[trusted]
fn main() {
    let mut vec = VecWrapper::new();
    vec.set(4, 55);
    println!("executed");

}

