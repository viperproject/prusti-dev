// ignore-test
// Seems like this works with PRUSTI_USE_MORE_COMPLETE_EXHALE=false...
#![allow(dead_code, unused)]
use prusti_contracts::*;

#[invariant_twostate(
    forall(|acct_id: u32|
        holds(Money(self.bank_id(), acct_id)) - old(holds(Money(self.bank_id(), acct_id))) ==
        PermAmount::from(self.balance_of(acct_id)) - PermAmount::from(old(self.balance_of(acct_id)))
    ))
]
#[invariant_twostate(self.bank_id() == old(self.bank_id()))]
struct Bank(u32);

type BankID = u32;

#[resource]
struct Money(BankID, u32);

impl Bank {

    #[pure]
    #[trusted]
    fn bank_id(&self) -> BankID {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    fn balance_of(&self, acct_id: u32) -> u32 {
        unimplemented!()
    }
}

fn on_recv_packet(
    bank: &mut Bank,
) {
}

#[requires(bank1.bank_id() !== bank2.bank_id())]
#[requires(transfers(Money(bank1.bank_id(), 0), 1))]
#[ensures(transfers(Money(bank1.bank_id(), 0), 1))]
fn send_preserves(bank1: &mut Bank, bank2: &mut Bank) {
    on_recv_packet(bank1);
}

fn main(){}
