use prusti_contracts::*;

type MemAddress = u32;

#[resource_kind]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(resource(Pointer(address), amt))]
#[ensures(resource(Pointer(address), amt))]
#[ensures(holds(Pointer(address)) >= PermAmount::from(3))]
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
