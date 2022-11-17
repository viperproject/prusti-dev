use prusti_contracts::*;

struct AccountID(u32);

struct Bank {

}

impl Bank {

    #[pure]
    #[trusted]
    fn balance_of(&self, acct_id: &AccountID) -> u32 {
        0
    }

    #[trusted]
    #[requires(amt >= 0 ==> u32::MAX - self.balance_of(acct_id) >= (amt as u32))]
    #[ensures(
        forall(|acct_id2: &AccountID|
          self.balance_of(acct_id2) ==
          if(acct_id === acct_id2 && amt >= 0) {
             old(self.balance_of(acct_id)) + (amt as u32)
          } else {
              0
          }
        )
    )]
    fn adjust_amount(&mut self, acct_id: &AccountID, amt: i32) {
    }

}


#[requires(amt < 0 && bank.balance_of(to) >= (0 - amt) as u32)]
fn go(bank: &mut Bank, to: &AccountID, amt: i32) {
    bank.adjust_amount(to, amt);
}

pub fn main(){}
