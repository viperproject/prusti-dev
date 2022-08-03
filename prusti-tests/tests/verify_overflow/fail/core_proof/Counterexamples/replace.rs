// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[ensures(result)]
fn replace(x: &mut i32, acc: bool) -> bool {
    match x {
        2 => {
            if acc {
                *x = 4;
                true
            } else {
                //panic!("no access"); 
                //panic!()
                false
            }
        }
        _ => true
    }
}

fn main() {}