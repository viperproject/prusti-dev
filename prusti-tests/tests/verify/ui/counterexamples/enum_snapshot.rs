use prusti_contracts::*;

#[derive(Copy, Clone)]
enum X{
    A(i32),
    B(f32),
}

#[pure]
fn equal(x: X) -> bool{
    match x{
        X::A(i) => i == 5,
        _ => true, 
    }
}

#[ensures(result)]
fn test(x: X, y: X) -> bool{
    equal(x)
}


fn main() {}