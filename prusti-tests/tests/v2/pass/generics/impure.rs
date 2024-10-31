use prusti_contracts::*;

pub fn test<T>(x: i8, y: T) -> T{ y }

fn main(){
    let a = test(-127, 11);
}
