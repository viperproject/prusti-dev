use prusti_contracts::*;

#[resource_kind]
struct Money(u32);

fn main(){
    produce!(forall(|x: u32| x < 5 ==> resource(Money(x), 1)));
    // consume!(forall(|x: u32| x < 3 ==> resource(Money(x), 1)));
}
