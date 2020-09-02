#![feature(box_syntax)]

extern crate prusti_contracts;

#[trusted]
fn random() -> u32 {
    unimplemented!()
}

fn test() {
    let mut x: Box<u32>;

    #[invariant="*x < 55"]
    'myloop: while {
        x = box random();
        if *x == 0 {
            break 'myloop;
        }
        *x < 55
    } {
        assert!(*x != 100);
    }

    assert!(*x == 0 || *x >= 55);
}

fn main() {}
