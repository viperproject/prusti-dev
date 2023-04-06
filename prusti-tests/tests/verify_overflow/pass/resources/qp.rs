use prusti_contracts::*;

#[resource]
struct Money(u32);

fn main(){
    produces!(forall(|x: u32| x < 5 ==> transfers(Money(x), 1)));
    // consumes!(forall(|x: u32| x < 3 ==> transfers(Money(x), 1)));
}
