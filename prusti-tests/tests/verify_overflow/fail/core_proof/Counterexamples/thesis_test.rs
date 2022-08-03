// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true
extern crate prusti_contracts;
use prusti_contracts::*;

//#[print_counterexample("[{}] -> {}", val, next)]
/*
struct LinkedList {
    val: i32,
    next: Option<Box<LinkedList>>,
}*/ 

#[derive(Clone, Copy)]
struct X{
    a: i32
}
/*
#[pure]
fn dummy(x: X) -> X{
    x
}*/
/*
#[pure]
#[ensures(result)]
fn equal2(l1: LinkedList, l2: LinkedList) -> bool{
    l1.val == l2.val
}*/
/*
#[trusted]
//#[ensures(l1.val == result)] //not working
fn deref(l1: Box<LinkedList>) -> LinkedList{
    *l1
}*/

/*
#[ensures(result)]
fn test(a: Seq<i32>) -> bool{
    a[0] == 0
}*/
/*
#[requires(l.val == 0)]
#[ensures(result)]
fn not_empty(l: LinkedList) -> bool {
    match l.next{
        Some(_) => false,
        None => true,
    }
}


#[requires(x.a == 0)]
#[ensures(result)]
fn always_equal(x: &X, y:X) -> bool {
    let tmp = dummy(x.clone());
    tmp.a == y.a
}


*/

#[requires(x.a == 0)]
#[ensures(result)]
fn always_equal(x: X, y: X) -> bool {
    let mut z = y;
    z.a = 1;
    x.a == z.a
}

fn main(){}