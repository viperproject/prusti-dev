#![allow(dead_code)]
use prusti_contracts::*;

#[resource]
struct Money();

trait Bank {

    #[pure]
    fn balance(&self) -> u32;

    #[ensures(transfers(Money(), amt))]
    #[ensures(
        holds(Money()) - old(holds(Money())) ==
        PermAmount::from(self.balance() - old(self.balance()))
    )]
    fn deposit(&mut self, amt: u32);

    #[requires(transfers(Money(), amt))]
    #[ensures(
        holds(Money()) - old(holds(Money())) ==
        PermAmount::from(self.balance() - old(self.balance()))
    )]
    fn withdraw(&mut self, amt: u32);
}

#[ensures(transfers(Money(), 10))]
fn client<B: Bank>(bank: &mut B) {
    bank.deposit(10);
    prusti_assert!(bank.balance() >= 10);
}

fn main() {

}
