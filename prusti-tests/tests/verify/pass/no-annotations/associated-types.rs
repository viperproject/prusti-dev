trait MyTrait {
    type MyType;

    fn foo(self: Self) -> Self::MyType;
}

struct S<E> { e: E }

impl<E> MyTrait for S<E> {
    type MyType = E;

    fn foo(self: Self) -> Self::MyType {
        self.e
    }
}

fn main() {
    let s: S<&'_ str> = S { e: "abc" };
    let k = s.foo();
}

