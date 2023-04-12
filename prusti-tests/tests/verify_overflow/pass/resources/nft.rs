// ignore-test
// Works in carbon, issue is because holds cannot be used in trigger
use prusti_contracts::*;

type AccountId = u32;
type TokenId = u32;

#[resource_kind]
struct CanChange(TokenId);

#[invariant_twostate(
    forall(
        |token_id: TokenId|
        (old(holds(CanChange(token_id))) == PermAmount::from(0) &&
         holds(CanChange(token_id)) == PermAmount::from(0)) ==>
            self.get_owner(token_id) == old(self.get_owner(token_id))
    )
)]
pub struct Keeper(u32, u32);

impl Keeper {
    #[pure]
    #[trusted]
    fn get_owner(&self, token_id: TokenId) -> Option<AccountId> {
        unimplemented!()
    }

    #[trusted]
    #[ensures(resource(CanChange(token_id), 1))]
    #[ensures(self.get_owner(token_id) == Some(acct_id))]
    fn obtain(&mut self, acct_id: AccountId, token_id: TokenId){
        unimplemented!()
    }

    fn borrow_unrelated(&mut self) -> &mut u32 {
        &mut self.1
    }

}

// fn client(keeper: &mut Keeper) {
//     keeper.borrow_unrelated();
// }


fn main(){}
