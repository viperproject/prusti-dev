/// Problem case #1: references assigned into a variable
///
/// Adapted from
/// [here](https://github.com/nikomatsakis/nll-rfc/blob/master/0000-nonlexical-lifetimes.md).
///
/// TODO: Add specifications.

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="self.lookup(old(index)) == old(value)"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

fn capitalize(vec: &mut VecWrapperI32) {
    let mut i = 0;
    let mut not_finished = i < vec.len();
    #[invariant="0 <= i && i <= vec.len()"]
    #[invariant="not_finished ==> i < vec.len()"]
    while not_finished {
        let value = vec.lookup(i);
        vec.store(i, value);
        i += 1;
        not_finished = i < vec.len();
    }
}

fn bar() {
    let mut data = VecWrapperI32::new();
    data.push(1);
    data.push(2);
    data.push(3);
    let slice = &mut data;
    capitalize(slice);
    data.push(4);
    data.push(5);
    data.push(6);
}

fn main() {
}
