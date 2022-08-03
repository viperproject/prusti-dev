use prusti_contracts::*;

#[derive(Clone, PartialEq)]
struct PeerList<T> {
    thing: T
}

#[extern_spec]
impl <T: Clone + Eq> Clone for PeerList<T> {
    #[ensures(some_property(self) ==> some_property(&result))]
    pub fn clone(&self) -> PeerList<T>;
}

#[pure]
#[trusted]
fn some_property<T>(list: &PeerList<T>) -> bool {
    panic!()
}

#[requires(some_property(t))]
fn go(t: &PeerList<u32>) {
    let t2 = t.clone();
    assert!(some_property(&t2));
}

fn main(){}
