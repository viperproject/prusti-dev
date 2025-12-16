fn foo<Y: MyTrait>(x: Y::SomeType<u32>) {}

trait MyTrait {
    type SomeType<X>;
}

struct St1 {}
struct St2 {}

impl MyTrait for St1 {
    type SomeType<X> = X;
}

impl MyTrait for St2 {
    type SomeType<X> = u64;
}

fn bar() {
    foo::<St1>(5);
}
