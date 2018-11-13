extern crate prusti_contracts;

struct T(u32);

struct G {
    value: T,
}

fn test(y: &mut G) {
    let mut x = &mut *y;
    let f = &mut x.value;
    x = &mut *y;
    use_both(f, &mut x.value);
}

fn use_both(_f: &mut T, _g: &mut T) {

}

fn main() {
}
