#![allow(dead_code, unused)]
use std::convert::TryInto;
use prusti_contracts::*;

#[pure]
#[trusted]
fn is_escrow_account(acct_id: AccountID) -> bool {
    unimplemented!()
}

type Coin = u32;
type AccountID = u32;

trait Bank {

    #[pure]
    fn unescrowed_coin_balance(&self) -> u32;

    predicate! {
        fn transfer_tokens_post(
            &self,
            old_bank: &Self,
            from: AccountID,
            to: AccountID
        ) -> bool {
        ((is_escrow_account(to) && !is_escrow_account(from)) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance() - 1) &&
        ((!is_escrow_account(to) && is_escrow_account(from)) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance() + 1) &&
        ((is_escrow_account(to) == is_escrow_account(from)) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance())
        }
    }

    #[ensures(self.transfer_tokens_post(
        old(self),
        from,
        to,
    ))]
    fn transfer_tokens(
        &mut self,
        from: AccountID,
        to: AccountID
    ) {
        self.burn_tokens(from);
        self.mint_tokens(to);
    }

    predicate! {
        fn burn_tokens_post(
            &self,
            old_bank: &Self,
            acct_id: AccountID
        ) -> bool {
        (!is_escrow_account(acct_id) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance() - 1) &&
        (is_escrow_account(acct_id) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance()) 
        }
    }

    #[ensures(self.burn_tokens_post(old(self), to))]
    fn burn_tokens(&mut self, to: AccountID);

    predicate! {
        fn mint_tokens_post(
            &self,
            old_bank: &Self,
            acct_id: AccountID
        ) -> bool {
        (!is_escrow_account(acct_id) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance() + 1) &&
        (is_escrow_account(acct_id) ==>
              self.unescrowed_coin_balance() ==
                old_bank.unescrowed_coin_balance())
        }
    }

    #[ensures(self.mint_tokens_post(old(self), to))]
    fn mint_tokens(&mut self, to: AccountID);
}

pub fn main(){}
