extern crate prusti_contracts;

struct G {
    value: u32,
}

fn test(y: &mut G) {
    let mut x = &mut *y;
    let f = &mut x.value;
    x = &mut *y;
    use_one(f);
}

/*

fn test41(y: &mut G) {
    let mut x = &mut *y;
    let f = &mut x.value;
    x = &mut *y;
    use_one(f);
    //let f2 = &mut x.f;
}

*/
fn use_one(_f: &mut u32) {}

fn main() {
}
