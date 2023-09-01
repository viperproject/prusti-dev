//@run
use prusti_contracts::*;

trait Shape {
    type T;
    fn area(&self) -> Self::T;
}

struct Rectangle<T> {
    height: T,
    width: T,
}

impl<T> Shape for Rectangle<T>
where
    T: std::ops::Mul<Output = T> + Copy,
{
    type T = T;
    fn area(&self) -> T {
        self.height * self.width
    }
}

#[trusted]
#[insert_runtime_check]
#[refine_spec(where S: PartialOrd, [
    ensures(result.1 >= result.0)
])]
fn area_pair<S>(a: &dyn Shape<T = S>, b: &dyn Shape<T = S>) -> (S, S) {
    (a.area(), b.area())
}


#[trusted]
fn main() {
    let r1 = Rectangle { height: 6, width: 10};
    let r2 = Rectangle { height: 5, width: 10};
    // larger one is passed first -> fails!
    area_pair(&r2, &r1);
}
