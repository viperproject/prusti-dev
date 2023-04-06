// ignore-test
// Works in carbon, issue is because holds cannot be used in trigger
use prusti_contracts::*;

type AccountId = u32;
type TokenId = u32;

#[resource]
struct Holds(AccountId, TokenId);

#[invariant_twostate(
    forall(
        |acct_id: AccountId, token_id: TokenId|
        holds(Holds(acct_id, token_id)) == PermAmount::from(1) ==>
            self.get_owner(token_id) == acct_id
    )
)]
pub struct Keeper(u32);

impl Keeper {
    #[pure]
    #[trusted]
    fn get_owner(&self, token_id: TokenId) -> AccountId {
        unimplemented!()
    }

    #[trusted]
    #[ensures(transfers(Holds(acct_id, token_id), 1))]
    fn obtain(&mut self, acct_id: AccountId, token_id: TokenId){
        unimplemented!()
    }

    #[ensures(self.get_owner(token_id) == acct_id)]
    fn obtain2(&mut self, acct_id: AccountId, token_id: TokenId){
        self.obtain(acct_id, token_id);
        prusti_assert!(holds(Holds(acct_id, token_id)) == PermAmount::from(1));
        prusti_assert!(self.get_owner(token_id) == acct_id);
    }
}


fn main(){}
