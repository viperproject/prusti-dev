enum AnyClientState {
    Tendermint(u32)
}

fn prepare_client(client_state: &AnyClientState) -> Result<u32, u64> {
    let r = match client_state {
        AnyClientState::Tendermint(cs) => cs,
        _ =>  return Err(0)
    };
    panic!() //~ ERROR panic!(..) statement might be reachable
}

fn main() {
}
