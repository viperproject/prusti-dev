use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(transfers(Pointer(address), amt))]
#[ensures(transfers(Pointer(address), 1))]
#[ensures(transfers(Pointer(address), 2))]
#[ensures(holds(Pointer(address)) == PermAmount::from(2))] //~ ERROR postcondition might not hold
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
