use prusti_contracts::*;

#[pure]
fn id<T>(x: T) -> T {
    x
}

#[pure]
fn main(){
    let x = id(1);
    let y = id(2);
    let z = x + y;
}
