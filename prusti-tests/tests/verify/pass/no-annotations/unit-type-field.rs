#[derive(Clone,Copy)]
struct UnitBox {
    unit: ()
}

#[derive(Clone,Copy)]
struct MyBox {
    val: i32,
    ghost: UnitBox,
    dummy: UnitBox,
}

fn copy(x: MyBox) -> MyBox {
    let y = x;
    let z = x;
    y
}

fn main() {}
