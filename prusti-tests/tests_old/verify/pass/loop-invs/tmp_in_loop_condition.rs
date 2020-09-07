#![feature(box_syntax)]

extern crate prusti_contracts;

#[trusted]
fn random() -> u32 {
    unimplemented!()
}

fn test() {
    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    while {
        let guard = random() < 55;

        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;

        guard
    } {
        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;
    }

    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    assert!(true);
}

fn main() {}
