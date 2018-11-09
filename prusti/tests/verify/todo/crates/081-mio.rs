#![feature(box_syntax, box_patterns)]

/// Source: https://carllerche.github.io/mio/src/mio/event_imp.rs.html
extern crate prusti_contracts;

pub struct Token(pub usize);

pub struct Ready(usize);

pub struct Event {
    kind: Ready,
    token: Token
}

pub fn kind_mut(event: &mut Event) -> &mut Ready {
    &mut event.kind
}

fn main() {}
