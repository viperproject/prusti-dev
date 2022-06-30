// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


/*
#[trusted]
struct BoxWrapper<T> {
    value: Box<T>,
}


#[model]
struct BoxWrapper<#[concrete] i32> {
    value: i32,
}


#[trusted]
#[ensures(b.model().value == val )]
fn set_box(b: &mut BoxWrapper<i32>, val: i32) {
    b.value = Box::new(val);
}

#[trusted]
#[ensures(result == b.model().value)]
fn get_box(b: BoxWrapper<i32>) -> i32{
    *b.value
}
*/

struct LinkedList {
    val: i32,
    next: Box<LinkedList>,
} 

/*
#[ensures(x.model().value == 0)]
fn test_1(x: BoxWrapper<i32>) -> i32 {
    get_box(x)
}
*/

#[ensures(!result)]
fn test_2(x: LinkedList) -> bool {
    x.val == 0
}



fn main(){}