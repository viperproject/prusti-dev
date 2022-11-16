use prusti_contracts::*;

#[pure]
#[trusted]
fn u8_is_ascii(byte: u8) -> bool {
    byte.is_ascii()
}

predicate! {
    fn is_ascii(bytes: &[u8]) -> bool {
        forall(|index: usize| index < bytes.len() ==> u8_is_ascii(bytes[index]))
    }
}

fn main() {}
