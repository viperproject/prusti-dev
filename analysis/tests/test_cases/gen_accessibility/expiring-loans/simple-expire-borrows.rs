struct G {
    value: u32,
}

struct F {
    f: G,
    g: G,
}

fn use_mut_ref(x: &mut G) {}

fn test1(x: F) {
    let mut y = x;
    let z = &mut y.f;
    use_mut_ref(z);
    let k = &mut y.f;
    //use_mut_ref(k);
}
