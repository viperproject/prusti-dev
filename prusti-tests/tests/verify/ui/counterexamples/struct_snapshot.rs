use prusti_contracts::*;

#[derive(Copy, Clone)]
struct X{
    a: i32, 
    b: i32,
    d: Y,
}

#[derive(Copy, Clone)]
struct Y{
    c: i32,
    e: Z
}

#[derive(Copy, Clone)]
struct Z{
    f: i32
}


#[pure]
fn equal(x: X) -> bool{
    x.a == x.b
}

//#[requires(y.c == x.d.c+1)]
#[requires(y.c == x.a)]
#[ensures(result)]
fn test(x: X, y: Y) -> bool{
    //let z = primitive_int(*x);
    //assert!(y.c == x.d.c);
    equal(x)
}
/*
#[ensures(result)]
fn test(x: X) -> bool{
    //let z = primitive_int(*x);
    equal(x)
}*/


fn main() {}