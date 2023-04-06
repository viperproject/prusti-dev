use prusti_contracts::*;
use std::cell::UnsafeCell;

#[invariant_twostate(old(holds(CanWrite(self.id()))) == PermAmount::from(0) ==> self.read() == old(self.read()))]
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
        unsafe {
            *self.field.get()
        }
    }

    fn nop(&mut self) -> u32 {
        0
    }

    #[requires(transfers(CanWrite(self.id()), 1))]
    #[ensures(self.read() == value)]
    #[ensures(transfers(CanWrite(self.id()), 1))]
    #[trusted]
    fn write(&self, value: u32) {
        unsafe {
            *self.field.get() = value;
        }
    }

    #[ensures(transfers(CanWrite(result.id()), 1))]
    #[trusted]
    fn new() -> IntRef {
        IntRef {
            field: UnsafeCell::new(0)
        }
    }
}

#[requires(transfers(CanWrite(int_ref.id()), 1))]
#[ensures(transfers(CanWrite(int_ref.id()), 1))]
#[ensures(int_ref.read() == 3)]
fn good_client(int_ref: &IntRef) {
    int_ref.write(3);
}

fn main() {
    let mut int_ref = IntRef::new();
    good_client(&int_ref);
    int_ref.nop();
    assert!(int_ref.read() == 3);
}
