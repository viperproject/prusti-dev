use prusti_contracts::*;

struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn test1(x: &mut F) -> &mut G {
    let y = reborrow(x);
    let z = reborrow(y);
    let z = reborrow(&mut *z);
    &mut z.f
}

fn test2(x: &mut F, b: bool) -> &mut G {
    let y = reborrow(&mut *x);
    let z = reborrow(y);
    let z2;
    if b {
        z2 = reborrow(z);
    } else {
        z2 = reborrow(x);
    }
    let z = reborrow(z2);
    let z = reborrow(z);
    &mut z.g
}

fn test3(x: &mut F, b: bool) -> &mut G {
    let y = reborrow(&mut *x);
    let z = reborrow(y);
    let z2;
    if b {
        z2 = &mut *z;
    } else {
        z2 = reborrow(x);
    }
    let z = reborrow(z2);
    let z = reborrow(z);
    &mut z.g
}

#[trusted]
fn reborrow(x: &mut F) -> &mut F {
    unimplemented!();
}

fn main() {
}
