use prusti_contracts::*;

#[resource]
struct Money(u32, u8);

#[requires(transfers(Money(123, 2), 1))]
fn spend(amt: u128){}

fn main(){
    prusti_assume!(transfers(Money(123,2), 5));
    spend(1);
    spend(1);
}
