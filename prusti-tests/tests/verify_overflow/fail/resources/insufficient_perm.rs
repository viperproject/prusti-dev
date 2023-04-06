use prusti_contracts::*;

#[resource]
struct Money(u32, u8);

#[requires(transfers(Money(123, 2), 1))]
fn spend(amt: u128){}

fn main(){
    spend(1); //~ ERROR insufficient permission
}
