//@ compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_unique_triggers_bound=30 -Passert_timeout=60000

use prusti_contracts::*;

#[trusted]
struct VecWrapper<T> {
    values: Vec<T>,
}

#[model]
struct VecWrapper<#[concrete] Tmp> {
    last_pushed: Tmp,
}

#[derive(Clone, Copy)]
struct Tmp {
    x: i32
}

#[trusted]
#[ensures(result.model().last_pushed.x == val )]
fn create_vec_wrapper_i32(val: i32) -> VecWrapper<Tmp>{
    let mut v = VecWrapper{
        values: Vec::new(),
    };
    let x = Tmp{x: val};
    v.values.push(x);
    v
}


#[trusted]
#[ensures(v.model().last_pushed.x == val )]
fn push_i32(v: &mut VecWrapper<Tmp>, val: i32) {
    let x = Tmp{x: val};
    v.values.push(x);
}


#[ensures(v.model().last_pushed.x == 5)] //~ERROR: postcondition might not hold.
fn len(v: VecWrapper<Tmp>){
    ()
}

#[trusted]
struct BoxWrapper<T> {
    value: Box<T>,
}

impl<T> BoxWrapper<T> {
    #[trusted]
    #[ensures(result.deref() === &value)]
    fn new(value: T) -> Self {
        Self { value: Box::new(value) }
    }
    #[pure]
    #[trusted]
    #[terminates]
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
    #[pure]
    #[terminates(trusted)]
    // FIXME: This function should be “predicate!”.
    #[ensures(result >= Int::from(1))]
    fn len(&self) -> Int {
        match &self.next {
            None => Int::from(1),
            Some(tail) => {
                tail.deref().len() + Int::from(1)
            }
        }
    }
    #[ensures((old(self.len()) + Int::from(1)) === result.len())]
    fn prepend(self, value: i64) -> Self {
        let len = self.len();
        let b = BoxWrapper::new(self);
        prusti_assert!(b.deref().len() == len);
        Self {
            val: value,
            next: Some(b),
        }
    }
    #[ensures((old(self.len()) + Int::from(1)) === result.len())]
    fn prepend2(self, value: i64) -> Self {
        let len = self.len();
        Self {
            val: value,
            next: Some(BoxWrapper::new(self)),
        }
    }
    #[pure]
    #[terminates(trusted)]
    #[ensures(Int::from(result) == self.len())]
    fn len_shared(&self) -> usize {
        match &self.next {
            None => 1,
            Some(tail) => {
                prusti_assume!(tail.deref().len() + Int::from(1) < Int::from(10));    // Avoid overflow check.
                prusti_assert!(Int::from(tail.deref().len_shared() + 1) === self.len());
                let result = tail.deref().len_shared() + 1;
                prusti_assert!(Int::from(result) === self.len());
                result
            }
        }
    }
    fn len_shared2(&self) -> usize {
        match &self.next {
            None => 1,
            Some(tail) => {
                tail.deref().len_shared2() + 1   //~ ERROR: attempt to add with overflow
            }
        }
    }
    fn len_mut2(&mut self) -> usize {
        match &mut self.next {
            None => 1,
            Some(tail) => {
                tail.deref_mut().len_mut2() + 1  //~ ERROR: attempt to add with overflow
            }
        }
    }
    #[pure]
    // FIXME: This function should be “predicate!”.
    #[requires(Int::from(0) <= index && index < self.len())]
    #[terminates(index)]
    fn lookup(&self, index: Int) -> Int {
        if index == Int::from(0) {
            Int::from(self.val)
        } else {
            prusti_assert!(
                Int::from(0) <= index &&
                index < self.len() &&
                index >= Int::from(1)
            );
            prusti_assert!(self.len() > Int::from(1));
            match &self.next {
                None => {
                    prusti_assert!(self.len() == Int::from(1));
                    unreachable!()
                },
                Some(tail) => {
                    tail.deref().lookup(index - Int::from(1))
                }
            }
        }
    }
}

#[trusted]
struct LinkedList2 {
    val: i64,
    next: Option<Box<LinkedList>>,
}

#[model]
struct LinkedList2 {
    values: Seq<Int>,
}

#[derive(Clone)]
struct Test{
    v: Seq<u32>,
}

fn main() {}
