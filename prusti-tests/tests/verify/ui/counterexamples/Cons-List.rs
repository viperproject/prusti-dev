// compile-flags: -Pcounterexample=true -Pcheck_overflow=false

use prusti_contracts::*;

/*pub mod my_mod{
    use prusti_contracts::*;
    pub enum List2 {
        Cons(i32, Box<List2>),  //check what happens if not int but ref (e.g. other struct)
        Nil,
    }

    /*struct X{
        a: i32,
    }*/

    }
}*/
/*
#[ensures(result)]
fn compare (l1: List, l2:List) -> bool{
    let x = l1.size();
    let y = l2.size();
    x>=y
}*/
/*
#[pure]
fn tmp (x: i32, y: i32) -> i32{
    if x == y{
        0
    } else {
        1
    }
}*/
/*#[ensures(result)]
fn tmp2 (x: i32, y: i32) -> bool{
    tmp(x) == tmp(y)
}*/

enum List2 {
    Cons(i32, Box<List2>),  //check what happens if not int but ref (e.g. other struct)
    Nil,
}
impl List2 {
    #[pure]
    #[ensures(result >= 0)]
    pub fn size(&self) -> i32{
        match &self {
            &List2::Nil => 0,
            &List2::Cons(_, tail) => 1 + tail.size(),
        }
    }   
}

#[ensures(result)]
fn compare2 (l1: List2, l2: List2) -> bool{
    //let l1 = List::Cons(1,Box::new(List::Nil));
    //let tmp = List2::Nil;
    l1.size() + 5 >= l2.size() 
    //tmp(l1.size(), y) >= tmp(l2.size(), y)
}



fn main() {}