// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

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
    assert!(value.1 == 2);
}

fn test2() {
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
    let value = unsafe { maybe.value }; //~ ERROR: the copied value may not be fully initialized.
}

pub enum MaybeUninit2 {
    Uninit(()),
    Value((i32, u32)),
}

fn test3() {
    let maybe = MaybeUninit2::Uninit(());
}

fn main() {}
