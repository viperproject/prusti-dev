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
//force specific counterexample
#[requires(v.model().values[Int::new(0)] == 9 )] 
#[requires(v.model().values[Int::new(1)] == 8 )]
#[requires(v.model().values[Int::new(2)] == 3 )]
#[requires(v.model().values[Int::new(3)] == 8 )]
fn test1(v: &VecWrapper<i8>) {
    assert!(v.lookup(0) + v.lookup(1) + v.lookup(2) + v.lookup(3) == 15)
}

#[requires(v.model().values.len() == Int::new(1) )]
#[requires(v.model().values[Int::new(0)] == 3 )] //force specific counterexample
#[ensures(v.model().values[0] == 1)]
fn test2(v: VecWrapper<i8>) {}

fn main(){}