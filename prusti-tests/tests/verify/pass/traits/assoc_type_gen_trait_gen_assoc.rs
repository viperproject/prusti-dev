fn foo<X, Y: MyTrait<X, Z>, Z>(x: Y::SomeType<SomeWrapper<X>>, y: Y::SomeOtherType, z: Y) {
    let res: X = z.gen();
}

trait MyTrait<T, T2> {
    type SomeType<A>;
    type SomeOtherType;

    fn gen(self) -> T;
}

struct St1<T> {
    x: T,
}
struct St2<T> {
    y: T,
}

impl<T, T2> MyTrait<T, T2> for St1<T> {
    type SomeType<A> = A;
    type SomeOtherType = T2;

    fn gen(self) -> T {
        self.x
    }
}

impl<T> MyTrait<T, T> for St2<T> {
    type SomeType<A> = T;
    type SomeOtherType = SomeWrapper<T>;

    fn gen(self) -> T {
        self.y
    }
}

fn bar() {
    foo::<f32, St1<f32>, u32>(SomeWrapper { val: 5.5 }, 6, St1 { x: 5.5 });
    foo::<bool, St2<bool>, bool>(true, SomeWrapper { val: false }, St2 { y: true });
}

struct SomeWrapper<T> {
    val: T,
}
