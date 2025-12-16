fn foo<X, Y: SomeTrait<X>>(x: Y::SomeOtherType<u32>) {}

trait SomeTrait<X> {
    type SomeType;
    type SomeOtherType<Y>;
}

impl<X> SomeTrait<X> for u32 {
    type SomeType = X;
    type SomeOtherType<Y> = Y;
}

fn bar() {
    foo::<f32, u32>(5);
}
