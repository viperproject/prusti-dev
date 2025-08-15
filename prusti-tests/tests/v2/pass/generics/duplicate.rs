struct Foo<T> {
    f: T,
}

fn foo<T>(a: Foo<T>, b: Foo<Foo<T>>) {}

fn main() {
    foo(
        Foo { f: 0 },
        Foo { f: Foo { f: 1 } },
    );
}
