// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[trusted]
struct VecWrapper<T> {
    values: Vec<T>,
}

#[model]
struct VecWrapper<#[concrete] i8> {
    values: Seq<i8>,
}

impl VecWrapper<i8> {
    #[trusted]
    #[requires(self.model().values.len() > Int::new(index))]
    #[ensures(self.model().values[Int::new(index)] == result)]
    fn lookup(&self, index: i64) -> i8 {
        self.values[index as usize]
    }
}


#[requires(v.model().values.len() == Int::new(4))]
//once -Pcheck_overflows works with sequences these lines can be removed 
#[requires(v.model().values[Int::new(0)] < 10 )] 
#[requires(v.model().values[Int::new(0)] > 0 )]
#[requires(v.model().values[Int::new(1)] < 10 )]
#[requires(v.model().values[Int::new(1)] > 0 )]
#[requires(v.model().values[Int::new(2)] < 10 )]
#[requires(v.model().values[Int::new(2)] > 0 )]
#[requires(v.model().values[Int::new(3)] < 10 )]
#[requires(v.model().values[Int::new(3)] > 0 )]
fn test1(v: &VecWrapper<i8>) {
    assert!(v.lookup(0) + v.lookup(1) + v.lookup(2) + v.lookup(3) == 15)
}

#[requires(v.model().values.len() == Int::new(1) )]
#[ensures(v.model().values[0] == 1)]
fn test2(v: VecWrapper<i8>) {}

fn main(){}