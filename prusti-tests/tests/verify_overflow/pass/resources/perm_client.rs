use prusti_contracts::*;

type MemAddress = u32;

#[resource]
struct Pointer(MemAddress);

#[requires(holds(Pointer(address)) == PermAmount::from(0))]
fn nop(address: MemAddress){
}

fn main(){
    let address: MemAddress = 1;
    prusti_assume!(transfers(Pointer(address), 1));
    nop(address);
}
