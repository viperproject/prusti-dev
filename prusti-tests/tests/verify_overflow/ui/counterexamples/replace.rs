// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

fn replace(x: &mut char, acc: bool) {
    match x {
        '$' => {
            if acc {
                *x = ' ';
            } else {
               panic!("no access"); 
            }
        }
        _ => {}
    }
}

fn main() {}
