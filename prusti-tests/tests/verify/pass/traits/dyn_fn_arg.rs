trait MyTrait {}

struct S { x: i32 }

impl MyTrait for S {}

fn consume(_v: &dyn MyTrait) {}

fn consume2(_v: &mut dyn MyTrait) {}

trait Foo<X> {}

impl<X> Foo<X> for S {}

fn consume3(_v: &dyn Foo<i32>) {}

fn consume4(_v: &dyn Foo<u32>) {}

