use prusti_contracts::*;

#[trusted]
fn random() -> Option<usize> {
    unimplemented!()
}

fn test() {
    loop {
        match random() {
            Some(_) => return,
            None => {}
        }
    }
}

fn main() {}
