extern crate prusti_contracts;

pub struct VecWrapperUSize{
    v: Vec<usize>
}

impl VecWrapperUSize {
    #[trusted]
    #[ensures="result.len() == 0"]
    fn new() -> Self {
        Self {
            v: Vec::new(),
        }
    }
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> usize {
        self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.lookup(index) == *result"]
    pub fn index(&self, index: usize) -> &usize {
        &self.v[index]
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn push(&mut self, value: usize) {
        self.v.push(value);
    }
}

#[pure]
fn fib(n: usize) -> usize {
    match n {
        0 => 0,
        1 => 1,
        k => fib(k-1) + fib(k-2),
    }
}

#[requires="m >= 2"]
#[ensures="m == result.len()"]
#[ensures="forall j: usize ::
                (0 <= j && j < result.len()) ==>
                result.lookup(j) == fib(j)"]
fn create_fib_array(m: usize) -> VecWrapperUSize {
    let mut fib_array = VecWrapperUSize::new();
    fib_array.push(0);
    fib_array.push(1);
    let mut i = 2;
    #[invariant="2 <= i"]
    #[invariant="i == fib_array.len()"]
    #[invariant="forall j: usize ::
                    (0 <= j && j < fib_array.len()) ==>
                    fib_array.lookup(j) == fib(j)"]
    while i != m {
        let a = *fib_array.index(i-2);
        let b = *fib_array.index(i-1);
        fib_array.push(a + b);
        i += 1;
    }
    fib_array
}

fn main() {}
