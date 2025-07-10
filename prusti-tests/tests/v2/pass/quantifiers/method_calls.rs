use prusti_contracts::*;

struct TestStructReference {
    len: usize,
}
struct TestStruct {
    len: usize,
}

impl TestStructReference {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn get(&self, idx: usize) -> i32 {
        unimplemented!()
    }
}
impl TestStruct {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn get(&self, idx: usize) -> i32 {
        unimplemented!()
    }
}

// Test method call on reference type within forall quantifier
// This tests the branch where has_ref_upvars is true (reference case)
#[requires(forall(|i: usize| i < res.len ==> res.get(i) >= 0))]
pub fn test1_ref_method_call(res: &TestStructReference) {}

// Test method call on owned type within forall quantifier
// This tests the branch where has_ref_upvars is false (owned case)
#[requires(forall(|i: usize| i < res.len ==> res.get(i) >= 0))]
pub fn test2_method_call(res: TestStruct) {}

fn main() {}
