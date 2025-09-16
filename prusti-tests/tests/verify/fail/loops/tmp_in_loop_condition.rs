use prusti_contracts::*;

#[trusted]
fn random() -> u32 {
    unimplemented!()
}

fn test1() {
    let mut tmp = Box::new(Box::new(random()));
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    while {
        let guard = random() < 55;

        let mut tmp = Box::new(Box::new(random()));
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;

        guard
    } {
        let mut tmp = Box::new(Box::new(random()));
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;
    }

    let mut tmp = Box::new(Box::new(random()));
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;
    assert!(false); //~ ERROR
}

fn test2() {
    let mut tmp = Box::new(Box::new(random()));
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    while {
        let guard = random() < 55;

        let mut tmp = Box::new(Box::new(random()));
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;

        guard
    } {
        let mut tmp = Box::new(Box::new(random()));
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;
        assert!(false); //~ ERROR
    }

    let mut tmp = Box::new(Box::new(random()));
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;
}

fn main() {}
