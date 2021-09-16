
struct Pos {
    x:u8,
    y:u8
}


fn foo() {

    let p = Pos {x:1, y:0};

    let d = p.x << 1;
    let e = p.y << 1;

    assert!(d + e == 2);
}
fn main() {}