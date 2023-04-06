use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(transfers(Pointer(address), amt))]
#[ensures(transfers(Pointer(address), 6))] //~ ERROR: might not have sufficient resource
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
