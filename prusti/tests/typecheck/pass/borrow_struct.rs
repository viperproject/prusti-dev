extern crate prusti_contracts;

/*
struct F<'a> {
    f: &'a mut u32,
}

struct T<'a> {
    f: &'a mut F<'a>,
}

fn use_t<'a, 'b>(x: &'a mut T<'b>) -> &'a mut F<'b> {
    x.f
}

fn borrow(_x: &mut u32) {
}

*/
fn reborrow(x: &mut u32) -> &mut u32 {
    x
}
fn test2() {}
/*

fn test() {
    let mut y = 4;
    let mut x = T {
        f: &mut F { f: &mut y, },
    };
    let z = use_t(&mut x);
    *(z.f) = 5;
    let mut s = 6;
    z.f = &mut s;       // TODO: Repackage the wand here to put s on the right hand side.

    let v = x.f;   // Make sure that this is a move.
    *(v.f) = 7;
    let _z = y;
    s = 8;
}

// This procedure is not supported because it has more than two layers
// of blocking (requires nested magic wands).
fn assign_f<'a, 'b>(x: &'a mut F<'b>, y: &'b mut u32) -> &'a mut u32 {
    x.f = y;
    x.f
}

*/
fn main() {
    let mut x = 4;
    let y = reborrow(&mut x);
    test2();
}
