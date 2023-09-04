use prusti_contracts::*;

fn main() {
    let foo = Foo { x: 1 };
    let bar = Bar { x: 2 };
    assert!(foo.clone().x == 1);
    assert!(bar.clone().x == 2);
}

#[derive(Clone)]
struct Foo {
    x: i32,
}

struct Bar {
    x: i32,
}

impl Clone for Bar {
    fn clone(&self) -> Self {
        Self { x: self.x }
    }
}
