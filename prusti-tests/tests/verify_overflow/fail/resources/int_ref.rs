use prusti_contracts::*;
use std::cell::UnsafeCell;

struct IntRef { field: UnsafeCell<u32> }

#[derive(Clone, Copy)]
struct IntRefId(u32);

#[resource]
struct CanWrite(IntRefId);

impl IntRef {

    #[pure]
    #[trusted]
    fn id(&self) -> IntRefId {
        unimplemented!();
    }

    #[pure]
    #[trusted]
    fn read(&self) -> u32 {
        unimplemented!();
    }

    #[requires(transfers(CanWrite(self.id()), 1))]
    #[ensures(self.read() == value)]
    #[ensures(transfers(CanWrite(self.id()), 1))]
    #[trusted]
    fn write(&self, value: u32) {
        unimplemented!()
    }

    #[ensures(transfers(CanWrite(result.id()), 1))]
    #[trusted]
    fn new() -> IntRef {
        unimplemented!()
    }
}

fn bad_client(int_ref: &IntRef) {
    int_ref.write(3); //~ ERROR: insufficient permission
}

fn main() {
    let int_ref = IntRef::new();
    bad_client(&int_ref);
}
