use prusti_contracts::*;

struct X{
    a: i32, 
    b: i32,
}

#[pure]
fn equal(x: &X) -> bool{
    x.a == x.b
}

/*
#[ensures(result)]
fn test(x: (i32, i32, char, char)) -> bool{
    //let z = primitive_int(*x);
    equal((x.2, x.1), (x.0, x.3))
}*/


#[requires(y.a == y.b)]
#[requires(z.a == 1)]
#[ensures(result)]
fn test(x: &&X, y: &&X, z:&X) -> bool{
    assert!(z.a == 1);
    equal(y);
    equal(x)
}


fn main() {}