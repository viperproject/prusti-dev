extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32{ v: vec![] }
    }

    #[trusted]
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures="self.lookup(old(index)) == old(value)"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }
}
