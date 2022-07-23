// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_unique_triggers_bound=30 -Passert_timeout=60000

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


#[ensures(v.model().last_pushed.x == 5)] //~ ERROR postcondition might not hold.
fn len(v: VecWrapper<Tmp>){
    ()
}

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
    #[pure]
    // FIXME: This function should be #[ghost].
    #[ensures(result >= Int::new(1))]
    fn len(&self) -> Int {
        match &self.next {
            None => Int::new(1),
            Some(tail) => {
                tail.deref().len() + Int::new(1)
            }
        }
    }
    #[pure]
    #[ensures(Int::new_usize(result) == self.len())]
    fn len_shared(&self) -> usize {
        match &self.next {
            None => 1,
            Some(tail) => {
                prusti_assume!(tail.deref().len() + Int::new(1) < Int::new(10));
                prusti_assert!(Int::new_usize(tail.deref().len_shared() + 1) == self.len());
                let result = tail.deref().len_shared() + 1;

                // FIXME: This is a bug, this function should verify.
                prusti_assert!(Int::new_usize(result) == self.len());   //~ ERROR: the asserted expression might not hold
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
// FIXME
//  #[ensures(Int::new_usize(result) == self.len())]
//  fn len_mut(&mut self) -> usize {
//      match &mut self.next {
//          None => 1,
//          Some(tail) => {
//              prusti_assume!(tail.deref().len() + Int::new(1) < Int::new(10));
//              let result = tail.deref_mut().len_mut() + 1;

//              // FIXME: This is a bug, this function should verify.
//              prusti_assert!(Int::new_usize(result) == self.len());   //: the asserted expression might not hold
//              result
//          }
//      }
//  }
    fn len_mut2(&mut self) -> usize {
        match &mut self.next {
            None => 1,
            Some(tail) => {
                tail.deref_mut().len_mut2() + 1  //~ ERROR: attempt to add with overflow
            }
        }
    }
    #[pure]
    // FIXME: This function should be #[ghost].
    #[requires(Int::new(0) <= index && index < self.len())]
    fn lookup(&self, index: Int) -> Int {
        if index == Int::new(0) {
            Int::new(self.val)
        } else {
            prusti_assert!(
                Int::new(0) <= index &&
                index < self.len() &&
                index >= Int::new(1)
            );
            prusti_assert!(self.len() > Int::new(1));
            match &self.next {
                None => {
                    prusti_assert!(self.len() == Int::new(1));
                    unreachable!()
                },
                Some(tail) => {
                    tail.deref().lookup(index - Int::new(1))
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
