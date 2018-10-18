/// Issue #75:
extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[ensures="result.len() == length"]
    #[ensures="forall i: usize :: (0 <= i && i < length) ==> result.lookup(i) == 0"]
    pub fn new(length: usize) -> Self {
        VecWrapperI32{ v: vec![0; length] }
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
    #[ensures="self.lookup(old(index)) == old(value)"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != old(index)) ==> self.lookup(i) == old(self.lookup(i))"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }
}

#[requires="1 < x.len() && 1 < y.len()"]
fn test1(x: VecWrapperI32, y: VecWrapperI32) {
    let z = x.lookup(0);
    assert!(0 <= x.len());
}

#[requires="1 < x.len() && 1 < y.len()"]
fn test2(x: VecWrapperI32, y: VecWrapperI32) {
    let z = x.lookup(0);
    //let w = x.lookup(1);
    assert!(0 <= x.len());
}

fn main() {

}
