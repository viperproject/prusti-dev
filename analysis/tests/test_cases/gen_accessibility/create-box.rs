#![feature(box_patterns)]
#![feature(box_syntax)]

fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    assert!(v == y);
    let z = Box::new(y);
    assert!(v == *z);
    let result = box *z;
    result
}
