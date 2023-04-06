use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(transfers(Pointer(address), amt))]
fn client(address: MemAddress, amt: u32){
    prusti_assert!(holds(Pointer(address)) == PermAmount::from(amt));
    prusti_assert!(holds(Pointer(address)) == PermAmount::from(amt));
}

fn main(){
}
