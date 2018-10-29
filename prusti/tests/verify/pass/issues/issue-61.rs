/// Issue #61: "Precondition of pure function `lookup` does not hold"

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
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }
}

#[requires="index >= 0"]
#[requires="forall i: usize :: (0 <= i && i < v.len()) ==> v.lookup(i) == 100"]
//#[ensures="index == old(index)"]
//#[ensures="default_val == old(default_val)"]
//#[ensures="if index < old(v.len()) { result == 100 } else { result == default_val }"]
fn extract(v: VecWrapperI32, index: usize, default_val: i32) -> i32 {
    if index < v.len() {
        assert!(index < v.len());
        v.lookup(index)
    } else {
        default_val
    }
}

#[trusted]
fn main(){
    println!("It works!");
}
