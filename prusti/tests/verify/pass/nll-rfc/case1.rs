/// Problem case #1: references assigned into a variable
///
/// Adapted from
/// [here](https://github.com/nikomatsakis/nll-rfc/blob/master/0000-nonlexical-lifetimes.md).
///
/// Some lower bounds could be omitted if `CHECK_BINARY_OPERATIONS` is
/// set to `true`.

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
    #[ensures="self.lookup(index) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

#[ensures="vec.len() == old(vec.len())"]
#[ensures="forall i: usize :: (0 <= i && i < vec.len()) ==> vec.lookup(i) <= 0"]
#[ensures=r"forall j: usize :: (0 <= j && j < vec.len() && old(vec.lookup(j)) > 0) ==>
                -old(vec.lookup(j)) == vec.lookup(j)"]
#[ensures=r"forall j: usize :: (0 <= j && j < vec.len() && old(vec.lookup(j)) <= 0) ==>
                old(vec.lookup(j)) == vec.lookup(j)"]
fn capitalize(vec: &mut VecWrapperI32) {
    let mut i = 0;
    let mut not_finished = i < vec.len();
    #[invariant="vec.len() == old(vec.len())"]
    #[invariant="0 <= i && i < vec.len()"]
    #[invariant="forall j: usize :: (0 <= j && j < i) ==> vec.lookup(j) <= 0"]
    #[invariant=r"forall j: usize :: (i <= j && j < vec.len()) ==>
                    old(vec.lookup(j)) == vec.lookup(j)"]
    #[invariant=r"forall j: usize :: (0 <= j && j < i && old(vec.lookup(j)) > 0) ==>
                    -old(vec.lookup(j)) == vec.lookup(j)"]
    #[invariant=r"forall j: usize :: (0 <= j && j < i && old(vec.lookup(j)) <= 0) ==>
                    old(vec.lookup(j)) == vec.lookup(j)"]
    while not_finished {
        let value = vec.lookup(i);
        if value > 0 {
            vec.store(i, -value);
        } else {
            vec.store(i, value);
        }
        i += 1;
        not_finished = i < vec.len();
    }
}

fn bar() {
    let mut data = VecWrapperI32::new();
    data.push(1);
    data.push(-2);
    data.push(3);
    let slice = &mut data;
    capitalize(slice);

    assert!(data.lookup(0) == -1);
    assert!(data.lookup(1) == -2);
    assert!(data.lookup(2) == -3);

    data.push(4);
    data.push(-5);
    data.push(6);

    assert!(data.lookup(0) == -1);
    assert!(data.lookup(1) == -2);
    assert!(data.lookup(2) == -3);
    assert!(data.lookup(3) == 4);
    assert!(data.lookup(4) == -5);
    assert!(data.lookup(5) == 6);
}

fn main() {
    bar();
}
