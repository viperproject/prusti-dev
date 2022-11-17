// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

enum X {
    V1(i32),
    V2(i32)
}

enum Y {
    V1{
        x: X,
        v: i32,
    },
    V2(i32),
}

fn test1(x: X){
    match x {
        X::V1(a) => assert!(false),      //~ ERROR: the asserted expression might not hold
        X::V2(a) => assert!(true),
    }
}

fn test2(c: char){
    match c {
        'a' => assert!(false),      //~ ERROR: the asserted expression might not hold
        _ => (),
    }
}

fn test3(){
    panic!()        //~ ERROR: panic!(..) statement might be reachable
}

fn test4(c: char){
    panic!()        //~ ERROR: panic!(..) statement might be reachable
}

fn test5(y: Y) {
    match y {
        Y::V1{ x, ..} => {
            let _z = x;
        }
        Y::V2(_) => {}
    }
}

fn main() {}
