// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true
extern crate prusti_contracts;
use prusti_contracts::*;
type Seq = prusti_contracts::Seq<i32>;

//#[print_counterexample("[{}] -> {}", val, next)]

#[trusted]
struct LinkedList {
    val: i32,
    next: Option<Box<LinkedList>>,
} 

#[derive(Clone)]
struct Test{
    v: Seq,
}
/*
#[model]
struct LinkedList {
    values: Seq,
}
*/
impl LinkedList{
    #[trusted]
    //#[ensures(self.model().values == Seq::concat(self.model().values, Seq::single(elem)))]
    fn append(&mut self, elem: i32){
        match self.next{
            Some(ref mut next) => (*next).append(elem),
            None => self.next = Some(Box::new(LinkedList{
                val: elem,
                next: None
            })),
        }
    }
}

#[ensures(seq == seq![1,2,3,4,5])]
fn indexing(seq: Seq) {
    //prusti_assert!(seq[2] == 3);
    //prusti_assert!(seq[3] == 5);
}


#[requires(x > 0)]
#[ensures(result != 2)]
fn fail (x: i32) -> i32 {
    let mut y = x;
    y = y + 1;
    y
}



fn main(){}