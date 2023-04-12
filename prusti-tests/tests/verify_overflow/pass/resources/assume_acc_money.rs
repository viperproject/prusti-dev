use prusti_contracts::*;

type AccountId = u8;

#[resource_kind]
struct Money(AccountId);

#[requires(resource(Money(acct_id), amt))]
fn spend(acct_id: AccountId, amt: u32){}

fn main(){
    let acct_id: AccountId = 1;
    prusti_assume!(resource(Money(acct_id), 10));
    spend(acct_id, 5);
    spend(acct_id, 5);
}
