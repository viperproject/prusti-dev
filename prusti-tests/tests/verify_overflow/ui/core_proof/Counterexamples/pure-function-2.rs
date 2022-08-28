// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[derive(Copy, Clone)]
struct X {
    a: i32
}

impl X {
    #[pure]
    fn get_a(&self) -> i32{
        self.a
    }
}


#[pure]
fn baz(x: X) -> X {
    X {a: x.a + 1}
}


fn test(x: i32, y: X) {
    //FIXME: Counterexample generation treats y.get_a() as an assignment for y and
    //produces a counterexample of y at that point
    let z = y.get_a();
    assert!(z == baz(y).a)
}


fn main(){}