// This example fails when vanilla single-state invariants are enabled, i.e.
// PRUSTI_ENABLE_TYPE_INVARIANTS=true

#![allow(dead_code, unused)]
use prusti_contracts::*;

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct PrefixedClassId(u32);

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct NFTPacketData {
    pub class_id: PrefixedClassId,
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Packet {
    pub data: NFTPacketData
}

#[pure]
pub fn mk_packet(
    data: NFTPacketData
) -> Packet {
    Packet {
        data,
    }
}

#[pure]
fn make_packet_data(class_id: PrefixedClassId) -> NFTPacketData {
    NFTPacketData {class_id}
}

fn send_nft(class_id: PrefixedClassId) -> Packet {
    let data = make_packet_data(class_id);
    mk_packet(data)
}

fn main(){}
