// compile-flags: -Pencode_bitvectors=true

pub mod m {

    use prusti_contracts::*;

    pub type B15 = [i8; 15];

    pub fn s(a: &mut B15) {
        let mut i: usize = 0;
        while i < 14 {
            body_invariant!(i < 14);
            let t1 = a[i + 1] + (a[i] >> 2u32);
            a[i + 1] = t1;
            let t2 = a[i] & 0x3f;
            a[i] = t2;
            i += 1;
        }
    }

    pub fn s_fail(a: &mut B15) {
        let mut i: usize = 0;
        while i < 14 {
            body_invariant!(i < 14);
            let t1 = a[i + 1] + (a[i] >> 2u32);
            a[i + 1] = t1;
            let t2 = a[i] & 0x3f;
            a[i] = t2;
            i += 1;
        }
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }

    pub type A15 = [u8; 15];

    pub fn f(a: &mut A15) {
        let mut i: usize = 0;
        while i < 14 {
            body_invariant!(i < 14);
            let t1 = a[i + 1] + (a[i] >> 2u32);
            a[i + 1] = t1;
            let t2 = a[i] & 0x3f;
            a[i] = t2;
            i += 1;
        }
    }

    pub fn f_fail(a: &mut A15) {
        let mut i: usize = 0;
        while i < 14 {
            body_invariant!(i < 14);
            let t1 = a[i + 1] + (a[i] >> 2u32);
            a[i + 1] = t1;
            let t2 = a[i] & 0x3f;
            a[i] = t2;
            i += 1;
        }
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }

    pub fn f_fail2(y: u8) {
        let z = y;
        let x: u32 = 6;
        let t1 = (x & 26);
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }

    pub fn f_fail3(y: i8) {
        let z = y;
        let x: i8 = 6;
        let t1 = (x & 26);
        assert!(false);     //~ ERROR: the asserted expression might not hold
    }
}

fn main() {}
