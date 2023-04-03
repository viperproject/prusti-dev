#![feature(box_patterns)]

fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    assert!(v == y);
    let z = Box::new(y);
    assert!(v == *z);
    let result = Box::new(*z);
    result
}
