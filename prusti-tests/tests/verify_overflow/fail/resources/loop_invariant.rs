use prusti_contracts::*;

#[resource_kind]
struct Money();  

#[invariant_twostate(
    PermAmount::from(self.0) - PermAmount::from(old(self.0)) ==
    holds(Money()) - old(holds(Money()))
)]
struct Bank(u32);

#[requires(bank.0 == 0)]
fn do_loop(bank: &mut Bank) {
    let mut x = 0; 
    while x < 5 {
        // TODO: Fix error location and message
        body_invariant!(bank.0 == x); //~ ERROR: internal
        bank.0 += 1;
        x += 1;
    }
}

fn main(){

}
