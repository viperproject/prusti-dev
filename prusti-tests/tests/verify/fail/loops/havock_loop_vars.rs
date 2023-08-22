use prusti_contracts::*;

#[trusted]
fn random() -> bool {
    unimplemented!()
}

fn test() {
    let mut y = None;
    let mut z = None;

    loop {
        let x = Box::new(5);
        if random() {
            y = Some(x);
        } else {
            z = Some(x);
        }
        assert!(false); //~ ERROR might not hold
    }
}

fn main() {}
