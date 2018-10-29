
fn use_ref(_r: &mut i32) {}

fn test() {
    let mut y = 5;
    let mut x;

    x = &mut y;
    use_ref(x);

    x = &mut y;
    use_ref(x);
}

fn main() {}
