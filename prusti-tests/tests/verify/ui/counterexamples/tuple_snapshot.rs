use prusti_contracts::*;

#[pure]
fn equal(x: (char, i32), y: (i32, char)) -> bool{
    x.0 == y.1
}

/*
#[ensures(result)]
fn test(x: (i32, i32, char, char)) -> bool{
    //let z = primitive_int(*x);
    equal((x.2, x.1), (x.0, x.3))
}*/


#[ensures(result)]
fn test(x: (i32, i32, char, char)) -> bool{
    //let z = primitive_int(*x);
    let y = (x.2, x.1);
    let z = (x.0, x.3);
    equal(y, z)
}


fn main() {}