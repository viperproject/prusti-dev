struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn consume_F(_f: F) {}

fn use_both(_f: &mut G, _g: &mut G) {}

fn either<'a>(f: &'a mut G, _g: &'a mut G) -> &'a mut G { f }

fn test3(y: &mut F) {
    let x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;
    use_both(f, g);
}

fn test3b(y: &mut F) {
    let x = &mut *y;
    let f = &mut x.f;
    let g = &mut x.g;

    let m = either(f, g);
}
