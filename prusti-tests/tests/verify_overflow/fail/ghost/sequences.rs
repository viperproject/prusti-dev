use prusti_contracts::*;

fn test1() {
    ghost! {
        let s0: Seq<u32> = Seq::empty();
        let one = 1;
        let s1: Seq<u32> = Seq::single(one);
        let s2: Seq<u32> = Seq::single(2);
        let s3: Seq<u32> = Seq::concat(Seq::empty(), Seq::empty());
        let s4: Seq<u32> = Seq::concat(s0, s1);
        assert!(s4 == s1);
    }
}

fn test2() {
    ghost! {
        assert!(Seq::single(0) == Seq::single(0));
    }
}

fn test3() {
    ghost! {
        assert!(Seq::single(1) == Seq::single(0)); // ~ERROR
    }
}

fn main() {}
