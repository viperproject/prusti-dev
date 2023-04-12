use prusti_contracts::*;

#[resource_kind]
struct Money(u32, u8);

#[requires(resource(Money(123, 2), 1))]
fn spend(_amt: u128){}

fn main(){
    prusti_assume!(resource(Money(123,2), 1));
    spend(1);
}
