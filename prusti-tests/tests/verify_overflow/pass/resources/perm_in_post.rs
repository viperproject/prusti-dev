use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(amt > 3)]
#[requires(transfers(Pointer(address), 10))]
#[ensures(transfers(Pointer(address), 3))]
#[ensures(holds(Pointer(address)) == PermAmount::from(3))]
fn client(address: MemAddress, amt: u32){
    consumes!(transfers(Pointer(address), 7));
}

fn main(){
}
