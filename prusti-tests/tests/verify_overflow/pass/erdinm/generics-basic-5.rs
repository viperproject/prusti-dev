use prusti_contracts::*;

struct Number<A, B, C> {
    a: A,
    b: B,
    c: C,
}


#[requires(-10_000 < arg.b && arg.b < 10_000)]
#[ensures(arg.b == old(arg.b) - 1000)]
fn test1<A, B>(arg: &mut Number<A, i32, B>) {
    arg.b -= 1000;
}

#[requires(-10_000 < arg.b.b && arg.b.b < 10_000)]
#[ensures(arg.b.b == old(arg.b.b) - 1000)]
fn test2<A, B, C, D>(arg: &mut Number<A, Number<B, i32, C>, D>) {
    arg.b.b -= 1000;
}

#[requires(arg.a.b == 3000)]
#[requires(arg.b.b == 5000)]
#[requires(arg.c.b == 7000)]
fn test3<X>(arg: &mut Number<Number<i8, i32, u8>, Number<i16, i32, i64>, Number<isize, i32, usize>>) {
    test1(&mut arg.a);
    test1(&mut arg.c);
    assert!(arg.a.b == 2000);
    assert!(arg.b.b == 5000);
    assert!(arg.c.b == 6000);
    test2(arg);
    //assert!(arg.a.b == 2000);
    assert!(arg.b.b == 4000);
    //assert!(arg.c.b == 6000);
}

fn main() {}
