use prusti_contracts::*;

type MemAddress = u32;

#[resource_kind]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(resource(Pointer(address), 10))]
#[ensures(resource(Pointer(address), 3))]
#[ensures(holds(Pointer(address)) == PermAmount::from(3))]
fn client(address: MemAddress, amt: u32){
    consume!(resource(Pointer(address), 7));
}

fn main(){
}
