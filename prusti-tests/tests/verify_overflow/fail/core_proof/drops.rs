// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=10 -Psmt_qi_bound_global_kind=20

use prusti_contracts::*;

struct T {
    f: u32,
}

struct T2 {
    f: u32,
}

struct T3 {
    g: T,
}

impl Drop for T {
    fn drop(&mut self) {}
}

fn test1() {
    {
        let a = T { f: 4 };
    }
    let b = T2 { f: 4 };
}

fn test2() {
    let b = T2 { f: 4 };
    assert!(b.f == 5);  //~ ERROR the asserted expression might not hold
}

fn random() -> bool {
    false
}

fn test3() {
    let a = T { f: 4 };
    if random() {
        let _b = a;
    }
}

fn test4() {
    let a = T { f: 4 };
    if random() {
        let _b = a;
    }
    assert!(false);     //~ ERROR the asserted expression might not hold
}

fn test5() {
    let a = T { f: 4 };
    let b = T3 { g: a };
}

//fn test6() {
    //let a = T { f: 4 };
    //let b = T3 { g: a };
    //let mut c = 4;
    //let x = &mut c;
    //if random() {
        //drop(b.g);
        //*x = 5;
    //}
//}

fn main() {}

