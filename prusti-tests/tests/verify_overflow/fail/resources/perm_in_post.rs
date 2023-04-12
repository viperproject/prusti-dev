use prusti_contracts::*;

type MemAddress = u32;

#[resource_kind]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(resource(Pointer(address), amt))]
#[ensures(resource(Pointer(address), 1))]
#[ensures(resource(Pointer(address), 2))]
#[ensures(holds(Pointer(address)) == PermAmount::from(2))] //~ ERROR postcondition might not hold
fn client(address: MemAddress, amt: u32){
}

fn main(){
}
