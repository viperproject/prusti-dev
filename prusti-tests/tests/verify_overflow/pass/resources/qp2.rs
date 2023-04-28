#![allow(dead_code, unused)]
use prusti_contracts::*;

type TokenId = u32;

type PrefixedClassId = u32;

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct TokenIdVec(u32);

impl TokenIdVec {
    #[pure]
    #[trusted]
    #[ensures(forall(|j: usize| i != j ==> self.get(j) != result))]
    pub fn get(&self, i: usize) -> TokenId {
        unimplemented!()
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Packet {
    pub token_ids: TokenIdVec
}

impl Packet {

    #[pure]
    #[trusted]
    pub fn get_recv_class_id(&self) -> PrefixedClassId {
        unimplemented!()
    }

}


type Path = u32;



#[resource_kind]
pub struct Token(pub PrefixedClassId, pub TokenId);

#[requires(
    forall(|i : usize| i < 5 ==>
        resource(Token(packet.get_recv_class_id(), packet.token_ids.get(i)), 1)
    )
)]
pub fn on_recv_packet(
    packet: &Packet,
) {}

fn main() {
}
