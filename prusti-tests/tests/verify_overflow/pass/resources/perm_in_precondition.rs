use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(transfers(Pointer(address), amt))]
#[ensures(transfers(Pointer(address), amt))]
#[ensures(holds(Pointer(address)) == PermAmount::from(amt))]
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
