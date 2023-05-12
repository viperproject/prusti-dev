#![allow(dead_code, unused)]
use prusti_contracts::*;

type TokenId = u32;
type AccountId = u32;

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct PureVec<T>(T);

impl <T: Copy> PureVec<T> {

    #[pure]
    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> PureVec<T> {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    pub fn len(&self) -> usize {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    #[requires(i < self.len())]
    pub fn get(&self, i: usize) -> T {
        unimplemented!()
    }

}

pub type TokenIdVec = PureVec<TokenId>;

#[resource_kind]
pub struct Token(pub TokenId);

#[macro_export]
macro_rules! transfers_token { ($token_id:expr) => { resource(Token($token_id), 1) } }

#[invariant_twostate(
    forall( |token_id: TokenId|
    ( old(holds(Token(token_id))) == PermAmount::from(0) 
    &&    holds(Token(token_id)) == PermAmount::from(0)) ==>
        self.get_owner(token_id) == old(self.get_owner(token_id))
        // triggers = [(self.get_owner(class_id, token_id))]
))]
pub struct NFTKeeper(u32);

impl NFTKeeper {

    #[pure]
    #[trusted]
    pub fn get_owner(&self, token_id: TokenId) -> Option<AccountId> {
        unimplemented!()
    }

    #[trusted]
    #[ensures(transfers_token!(token_id))]
    pub fn mint(&mut self, token_id: TokenId) {
        unimplemented!()
    }
}


#[requires(
    forall(|i : usize, j: usize| i < token_ids.len() && j < i ==>
        token_ids.get(i) != token_ids.get(j)
))]
#[ensures(
    forall(|i : usize| i < token_ids.len() ==>
        transfers_token!(
            token_ids.get(i)
        )
    )
)]
pub fn on_recv_packet(
    nft: &mut NFTKeeper,
    token_ids: TokenIdVec,
) {
    let mut i = 0;
    while i < token_ids.len() {
        body_invariant!(i <= token_ids.len());
        body_invariant!(
            forall( |token_id: TokenId|
            ( old(holds(Token( token_id))) == PermAmount::from(0) 
            &&    holds(Token( token_id)) == PermAmount::from(0)) ==>
                nft.get_owner( token_id) == old(nft.get_owner( token_id))
            ));
        body_invariant!(
                forall(|j: usize| j < i ==>
                    transfers_token!(
                        token_ids.get(j)))
        );

        nft.mint(token_ids.get(i));
        i += 1;
    }
}

fn main() {
}
