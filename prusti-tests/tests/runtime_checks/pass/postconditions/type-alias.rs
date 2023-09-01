//@run
use prusti_contracts::*;
#[derive(Clone)]
struct SomeStruct<T> {
    pub x: T
}

type TypeAlias<'a, T> = &'a mut SomeStruct<T>;

fn main() {
    let mut s1 = SomeStruct { x: 2};
    let mut s2 = SomeStruct { x: 3};
    foo(&mut s1, &mut s2);
}

#[trusted]
#[insert_runtime_check]
#[ensures(old(x.x) == y.x)]
fn foo<T: PartialEq + Copy>(x: TypeAlias<T>, y: TypeAlias<T>) {
    y.x = x.x;
}
