#![allow(dead_code, unused)]
use std::convert::TryInto;
use std::collections::HashMap;
use std::hash::Hash;
use prusti_contracts::*;

type AcctId = u32;

#[extern_spec]
impl <T> std::option::Option<T> {

    #[pure]
    #[ensures(
        result === match self {
            Some(v) => v,
            None => default,
        }
    )]
    pub fn unwrap_or(self, default: T) -> T;
}


struct U32Map<T>(HashMap<T, u32>);

impl U32Map<AcctId> {

    #[pure]
    #[trusted]
    fn get(&self, key: AcctId) -> Option<u32> {
        self.0.get(&key).cloned()
    }

    #[ensures(matches!(self.get(key), Some(_)))] // This seems to be necessary for some reason
    #[ensures(self.get(key) == Some(value))]
    #[ensures(forall(|k: AcctId| k !== key ==> self.get(k) === old(self.get(k)), triggers =[(self.get(k))]))]
    #[trusted]
    fn insert(&mut self, key: AcctId, value: u32) {
        self.0.insert(key, value);
    }
}

#[resource_kind]
struct Money(AcctId);

#[invariant_twostate(
    forall(|acct_id: AcctId|
        holds(Money(acct_id)) -
        old(holds(Money(acct_id))) ==
        PermAmount::from(self.balance(acct_id)) -
            PermAmount::from(old(self.balance(acct_id)))
    ))
]
// Another useful invariant
#[invariant(
    forall(|acct_id: AcctId|
        PermAmount::from(self.balance(acct_id)) >= holds(Money(acct_id))
    ))
]
struct Bank(U32Map<AcctId>);



impl Bank {

    #[pure]
    fn balance(&self, acct_id: AcctId) -> u32 {
        self.0.get(acct_id).unwrap_or(0)
    }

    #[ensures(resource(Money(acct_id), amt))]
    fn deposit(&mut self, acct_id: AcctId, amt: u32) {
        let bal = self.balance(acct_id);
        self.0.insert(acct_id, bal + amt);
        produce!(resource(Money(acct_id), amt));
    }

    #[requires(resource(Money(acct_id), amt))]
    fn withdraw(&mut self, acct_id: AcctId, amt: u32) {
        let bal = self.balance(acct_id);
        self.0.insert(acct_id, bal - amt);
        consume!(resource(Money(acct_id), amt));
    }
}

#[requires(resource(Money(from), amt))]
#[ensures(resource(Money(to), amt))]
fn transfer(bank: &mut Bank, from: AcctId, to: AcctId, amt: u32) { 
    bank.withdraw(from, amt);
    bank.deposit(to, amt);
}

pub fn main(){}
