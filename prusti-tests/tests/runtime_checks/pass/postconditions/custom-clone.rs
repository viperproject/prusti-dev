//@run
use prusti_contracts::*;

struct SomeStruct {
    pub v: Vec<i32>,
}

impl SomeStruct {
    #[pure]
    #[trusted]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[pure]
    #[trusted]
    #[insert_runtime_check]
    #[requires(el < self.len())]
    pub fn lookup(&self, el: usize) -> i32 {
        self.v[el]
    }

    #[trusted]
    #[insert_runtime_check]
    #[ensures(old(self.len()) + 1 == self.len())]
    #[insert_runtime_check]
    #[ensures(self.lookup(self.len() - 1) == el)]
    pub fn push(&mut self, el: i32) {
        self.v.push(el);
    }
}

// a custom clone implementation that is not
// actually used in our code, but will be used
// to check old expressions
impl Clone for SomeStruct {
    #[trusted]
    fn clone(&self) -> SomeStruct {
        println!("custom clone is called");
        SomeStruct {
            v: self.v.clone(),
        }
    }
}

#[trusted]
fn main() {
    let mut s = SomeStruct {
        v: vec![1,2,3,4],
    };
    s.push(5);
}

