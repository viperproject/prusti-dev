use prusti_contracts::*;

// Borrows are not stable since rustc::Loan indicies aren't
// i.e. the `N` used in `DeadBorrowToken$(N)` for wands
// will differ between compilation
// This includes fns which return borrows, or e.g. slices
// where the fold-unfold algorithm doesn't handle the exhale well

// TODO: re-enable closure features

struct Struct {
    f1: u8,
    f2: Box<Enum>,
}
enum Enum {
    Opt1,
    Opt2(i16),
    Opt3(Struct),
}
trait Trait<Tp> {
    #[requires(true)]
    #[ensures(false)]
    fn fn1(a: ());
    fn fn5(x: Tp) -> Tp { x }
    fn fn7(&self, t: (i16, i16)) -> i16;
    fn fn8(self, t: &(u8, u8)) -> u8;
}
impl Trait<i8> for Struct {
    fn fn1(o: ()) { Struct::fn5(0); o }
    fn fn7(&self, (a, _b): (i16, i16)) -> i16 { a }
    fn fn8(self, _t: &(u8, u8)) -> u8 { 
        assert!(self.f1 > 10);
        self.f1
    }
}
impl<A> Trait<A> for Enum {
    fn fn1(_m: ()) {}
    fn fn5(x: A) -> A { Struct::fn1(()); x }
    fn fn7(&self, t: (i16, i16)) -> i16 {
        match self {
            Enum::Opt1 => t.0,
            Enum::Opt2(i) => *i,
            Enum::Opt3(_s) => t.1,
        }
    }
    fn fn8(self, (_a, b): &(u8, u8)) -> u8 { *b }
}

fn main() {
    fn1();
    let mut arr = [0, 4, 9, 11, -9, -11];
    let i = 99;
    assert!(i + 2 == 100);
    let e = Enum::Opt2(-2);
    fn6::<3>(&mut arr, &i, &e);
    // e.fn8(); -> Fold-unfold error
    fn8(Enum::Opt2(-2));
    //let b = Box::new(Enum::Opt1);
    /*
    let cl = closure!(
        #[requires(i > 10)]
        #[ensures(if let Enum::Opt3(s) = result { s.f1 == i } else { false })]
        |i:u8| -> Enum {
            Enum::Opt3(
                Struct {
                    f1: i,
                    f2: Box::new(Enum::Opt1) //b
                }
            )
        }
    );
    fn7(cl);
    */
}

fn fn1() { fn2(-3); }

#[requires(forall(|a:i32| exists(|b:i32| a-2 > -5 && a*5 < 5 && b == 5 ==> x < a)))]
#[ensures(forall(|a:i32| result == a))]
fn fn2(x: i32) -> i32 {
    let b = Box::new(Enum::Opt1);
    let mut s = Struct{ f1: 0, f2: b };
    fn4(&mut s);
    let tpl = (0, 8);
    let v = s.fn8(&tpl);
    -x + v as i32
}

#[pure]
fn fn3(s: &Struct, idx: u64) -> u8 {
    if idx == 0 { s.f1 }
    else {
        match &*s.f2 {
            Enum::Opt1 => 0,
            Enum::Opt2(_i) => 0,
            Enum::Opt3(s) => fn3(s, idx-1),
        }
    }
}

predicate!{
    fn p1(s: &Struct) -> bool {
        forall(|i: u64| fn3(s, i) == 0)
    }
}

#[requires(p1(s))]
#[ensures(!p1(s))]
fn fn4<'a>(s: &'a mut Struct) {
    s.f1 = fn5(s.f1);
    let v = s.fn7((5, 1));
    s.f2 = Box::new(Enum::Opt2(v));
}

fn fn5<T>(x: T) -> T { x }

#[requires(a.len() > 2)]
#[ensures(result.len() == 2)]
fn fn6<'a, 'b, const SZ: i16>(a: &'a mut [i16; 6], b: &'b i16, c: &'a Enum) -> [i16; 2] where 'a: 'b {
    a[0] = 1;
    let cv = <Enum as Trait<Enum>>::fn7(c, (0, 2));
    let d = [*b, cv];
    assert!(d[0] == 9);
    [d[0], a[2]]
}

/*
#[requires(cl |= |a: u8| [
    requires(a >= 20),
    ensures(true)
])]
fn fn7<F: FnOnce(u8) -> Enum>(cl: F) {
    let e = cl(22);
    let cl2 = closure!(
        #[requires(i > 2)]
        #[ensures(result == (i < 10))]
        |i:u8| -> bool { i < 10 }
    );
    let mut i = 3;
    'l1: while cl2(i) {
        body_invariant!(i < 10);
        i += 1;
        'l2: loop {
            body_invariant!(i == 1);
            if i > 3 {
                break 'l1
            } else {
                // break 'l2 -> Prusti panic
                continue 'l2
            }
        }
    }
    assert!(i == 10);
    fn8(e);
}
*/

fn fn8(e: Enum) {
    let tpl = (11, 2);
    let v = <Enum as Trait<bool>>::fn8(e, &tpl);
    assert!(v < 10);
    fn2(v.into());
}
