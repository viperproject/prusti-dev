use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(transfers(Pointer(address), amt))]
#[ensures(transfers(Pointer(address), amt))]
#[ensures(holds(Pointer(address)) >= PermAmount::from(3))]
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
