use prusti_contracts::*;

#[derive(Clone, Copy)]
struct AccountId(u8);

#[resource]
struct Money(AccountId);

#[requires(transfers(Money(acct_id), amt))]
fn spend(acct_id: AccountId, amt: u32){}

fn main(){
    let acct_id = AccountId(1);
    prusti_assume!(transfers(Money(acct_id), 10));
    spend(acct_id, 5);
}
