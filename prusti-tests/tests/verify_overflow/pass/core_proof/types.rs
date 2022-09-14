// compile-flags: -Punsafe_core_proof=true -Pverify_types=true
// -Puse_snapshot_parameters_in_predicates=true

use prusti_contracts::*;

struct T1 {}

struct T2 {
    f: T1,
    g: T1,
}

struct T3<T2> {
    f: T1,
    g: T2,
}

struct T4<'a> {
    f: &'a mut T1,
    //g: &'a T1,
}

struct T5<'a, 'b, 'c> {
    f: &'a mut T1,
    g: &'c mut T4<'b>,
    //h: &'a T1,
    //i: &'c T4<'b>,
}

//struct T6<'a, 'b, 'c> {
    //f: &'a mut T1,
    //g: &'a mut &'b mut T1,
    //h: &'a mut &'b mut &'c mut T1,
    //i: &'a T1,
    //j: &'a &'b T1,
    //k: &'a &'b &'c T1,
//}

//struct T7<'a> {
    //f: &'a mut T1,
    //g: &'a mut &'a mut T1,
    //h: &'a mut &'a mut &'a mut T1,
    //i: &'a T1,
    //j: &'a &'a T1,
    //k: &'a &'a &'a T1,
//}

//struct T8 {
    //f: [i32; 10],
    //g: [[T2; 10]; 10],
    //h: [[[T2; 10]; 10]; 10],
//}

//enum T9 {
    //F([i32; 10]),
    //G([[T2; 10]; 10]),
    //H([[[T2; 10]; 10]; 10]),
//}

//struct T10 {
    //f: [T8; 10],
    //g: [[T8; 10]; 10],
    //h: [[[T9; 10]; 10]; 10],
//}

//struct T11<'a, 'b, 'c, 'd> {
    //f: &'a mut [&'b mut T8; 10],
    //g: &'a mut [&'b mut [&'c mut T9; 10]; 10],
    //h: &'a mut [&'b mut [&'c mut [&'d mut T9; 10]; 10]; 10],
    //i: &'a [&'b T8; 10],
    //j: &'a [&'b [&'c T9; 10]; 10],
    //k: &'a [&'b [&'c [&'d T9; 10]; 10]; 10],
//}

//struct T12<'a> {
    //f: &'a mut [&'a mut T9; 10],
    //g: &'a mut [&'a mut [&'a mut T9; 10]; 10],
    //h: &'a mut [&'a mut [&'a mut [&'a mut T9; 10]; 10]; 10],
    //i: &'a [&'a T9; 10],
    //j: &'a [&'a [&'a T9; 10]; 10],
    //k: &'a [&'a [&'a [&'a T9; 10]; 10]; 10],
//}

//struct T13 {
    //f: (),
    //g: (T1, T2, T3<(T2, T1)>),
//}

//struct T14<'a, 'b, 'c> {
    //f: &'a mut (),
    //g: &'a mut (&'b mut T1, &'c mut T2),
    //i: &'a (),
    //j: &'a (&'b T1, &'c T2),
//}

struct T15<'a> {
    f: &'a mut [T1],
    g: &'a mut [T1; 10],
    //i: &'a [T1],
    //j: &'a [T1; 10],
}

//struct T16<'a, 'b> {
    //f: &'a mut [&'b mut T1],
    //g: &'a mut [&'b mut T1; 10],
    //i: &'a [&'b T1],
    //j: &'a [&'b T1; 10],
//}

//enum T17<'a, 'b> {
    //Left (&'a mut [T1; 10]),
    //Right (&'b mut [T2; 10]),
    //SharedLeft (&'a [T1; 10]),
    //SharedRight (&'b [T2; 10]),
//}

//enum T18<'a> {
    //Left(&'a mut [T1]),
    //Right([T2; 10]),
//}

//union T19<'a, 'b> {
    //f: &'a mut [&'b mut T1],
    //g: &'a mut [&'b mut T1; 10],
//}

//struct T20 {
    //f: *mut u8,
    //g: *mut [u8],
//}

#[trusted]
fn main() {}
