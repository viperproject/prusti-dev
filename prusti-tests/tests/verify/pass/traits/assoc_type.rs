fn foo<Y: MyTrait>(x: Y::SomeType) {}

trait MyTrait {
    type SomeType;
}

struct St1 {}
struct St2 {}

impl MyTrait for St1 {
    type SomeType = u32;
}

impl MyTrait for St2 {
    type SomeType = u64;
}

fn bar() {
    foo::<St1>(5);
}
