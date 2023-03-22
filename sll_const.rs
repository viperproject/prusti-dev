#![feature(core_intrinsics, rustc_attrs)]

fn main() {}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/const/cmain.dot")]
fn foo<T>(mut x: T, a: T, b: T, c: T, d: T) {
    return;
    let y = &mut x;
    let z = y as *mut _;

    unsafe {
        *z = b;
    }

    x = a;
}
