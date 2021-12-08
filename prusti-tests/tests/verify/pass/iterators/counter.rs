

// ignore-test: Fixed by PR 777 (https://github.com/viperproject/prusti-dev/pull/777)
// ignore-test: Remove explicit prohibiton of iterator usage in procedure_encoder.rs#encode_terminator
use prusti_contracts::*;

struct Counter {
    count: u32,
    up_to: u32,
}

#[refine_trait_spec]
impl Iterator for Counter {
    type Item = u32;

    #[ensures(self.up_to == old(self.up_to))]
    #[ensures(old(self.count) < self.up_to ==> is_some(&result) && unwrap(&result) == old(self.count))]
    #[ensures(old(self.count) >= self.up_to ==> is_none(&result))]
    #[ensures(is_some(&result) ==> self.count == old(self.count) + 1)]
    #[ensures(is_none(&result) ==> self.count == old(self.count))]
    fn next(&mut self) -> Option<u32> {
        if self.count < self.up_to {
            let res = create_some(self.count);
            self.count += 1;
            return res;
        }
        create_none()
    }
}


fn main() {
    let mut c = Counter {count: 0, up_to: 3};

    let el = c.next();
    assert!(is_some(&el));
    assert!(unwrap(&el) == 0);

    let el = c.next();
    assert!(is_some(&el));
    assert!(unwrap(&el) == 1);

    let el = c.next();
    assert!(is_some(&el));
    assert!(unwrap(&el) == 2);

    let el = c.next();
    assert!(is_none(&el));

    let el = c.next();
    assert!(is_none(&el));
}


// Option<u32> glue
#[trusted]
#[ensures(is_some(&result))]
#[ensures(unwrap(&result) == val)]
fn create_some(val: u32) -> Option<u32> {
    Some(val)
}

#[trusted]
#[ensures(is_none(&result))]
fn create_none() -> Option<u32> {
    None
}

#[trusted]
#[pure]
#[requires(is_some(o))]
fn unwrap(o: &Option<u32>) -> u32 {
    o.unwrap()
}

#[trusted]
#[pure]
#[ensures(matches!(*o, Some(_)) == result)]
fn is_some(o: &Option<u32>) -> bool {
    o.is_some()
}

#[trusted]
#[pure]
#[ensures(matches!(*o, None) == result)]
fn is_none(o: &Option<u32>) -> bool {
    o.is_none()
}