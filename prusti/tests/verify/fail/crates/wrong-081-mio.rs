/// Source: https://carllerche.github.io/mio/src/mio/event_imp.rs.html
extern crate prusti_contracts;

pub struct Token(pub usize);

pub struct Ready(usize);

pub struct Event {
    kind: Ready,
    token: Token
}

pub struct UnixReady(Ready);

#[ensures="false"]
pub fn kind_mut(event: &mut Event) -> &mut Ready { //~ ERROR
    &mut event.kind
}

impl UnixReady {
    #[ensures="false"]
    fn deref_mut(&mut self) -> &mut Ready { //~ ERROR
        &mut self.0
    }
}

fn main() {}
