// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


#[trusted]
struct BoxWrapper<T> {
    value: Box<T>,
}

impl<T> BoxWrapper<T> {
    #[trusted]
    fn new(value: T) -> Self {
        Self { value: Box::new(value) }
    }
    #[pure]
    #[trusted]
    fn deref(&self) -> &T {
        &self.value
    }
    #[trusted]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
    #[trusted]
    fn into_value(self) -> T {
        *self.value
    }
}

struct LinkedList {
    val: i64,
    next: Option<BoxWrapper<LinkedList>>,
}

impl LinkedList {
    fn prepend(self, value: i64) -> Self {
        Self {
            val: value,
            next: Some(BoxWrapper::new(self)),
        }
    }

    #[ensures(result >= Int::new(1))]
    fn len(&self) -> Int {
        match &self.next {
            None => Int::new(1),
            Some(tail) => {
                tail.deref().len() + Int::new(1)
            }
        }
    }
}

fn fail1(x: LinkedList, val: i64) {
    let y = LinkedList{
        val,
        next: Some(BoxWrapper::new(x)),
    };
    let z = y.prepend(val);
    assert!(z.val == 3)
}





/*
fn fail2(x: LinkedList, val: i64) {
    if x.len() == Int::new(1) {
        assert!(false)
    } 
}
*/
fn main(){}