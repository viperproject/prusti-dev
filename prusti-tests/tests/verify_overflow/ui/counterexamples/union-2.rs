// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

pub union MaybeUninit {
    uninit: (),
    value: (i32, u32),
}

fn test1() {
    let mut maybe = MaybeUninit {
        uninit: (),
    };
    #[allow(unused_must_use, unused_variables)]
    if false {
        #[prusti::spec_only]
        || -> bool { true };
        unsafe { prusti_set_union_active_field(std::ptr::addr_of!(maybe.value)) };
    }
    maybe.value.0 = 1;
    maybe.value.1 = 2;
    let value = unsafe { maybe.value };
    assert!(value.0 == 1);
    assert!(value.1 == 1);
}

fn main() {}
