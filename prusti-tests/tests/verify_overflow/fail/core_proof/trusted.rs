// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=20 -Psmt_qi_bound_global_kind=100

use prusti_contracts::*;

#[trusted]
struct GenericTrustedBox<T> {
    value: T,
}

impl<T> GenericTrustedBox<T> {
    #[trusted]
    fn new(value: T) -> Self {
        Self {
            value
        }
    }
    #[trusted]
    fn get_value(self) -> T {
        self.value
    }
}

fn test1() {
    let a = GenericTrustedBox::new(1);
    let _b = a;
}

fn test2<T>(a: GenericTrustedBox<T>) -> GenericTrustedBox<T> {
    let b = a;
    b
}

fn test3<T>(a: GenericTrustedBox<T>) -> GenericTrustedBox<T> {
    let b = a;
    let c = GenericTrustedBox::new(4);
    let _d = c;
    b
}

fn test4<T>(a: GenericTrustedBox<T>) -> GenericTrustedBox<T> {
    let b = a;
    let c = GenericTrustedBox::new(4);
    let d = c;
    assert!(d.get_value() == 4); //~ ERROR: the asserted expression might not hold
    b
}

#[trusted]
struct Refi32<'a, 'b: 'a> {
    f: &'a i32,
    g: &'b i32,
}

fn main() {}
