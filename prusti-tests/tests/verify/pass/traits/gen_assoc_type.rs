fn foo<Y: MyTrait>(x: Y::SomeType<u32>) {}

trait MyTrait {
    type SomeType<T>;
}

struct St1 {}
struct St2 {}

impl MyTrait for St1 {
    type SomeType<T> = SomeWrapper<T>;
}

impl MyTrait for St2 {
    type SomeType<T> = u64;
}

fn bar() {
    foo::<St1>(SomeWrapper { val: 5 });
}

struct SomeWrapper<T> {
    val: T,
}
