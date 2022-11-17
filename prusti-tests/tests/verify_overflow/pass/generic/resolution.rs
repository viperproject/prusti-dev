use prusti_contracts::*;

// Test generics and type parameter resolution at call sites. There are various
// aspects/features that can complicate a method call resolution:
//
// 1. type parameters in the signature of the method
// 2. lifetime parameters in the signature of the method
// 3. type parameters in the impl block containing the method (= its struct)
// 4. lifetime parameters in the impl block containing the method (= its struct)
// 5. the method belongs to a trait
// 6. associated types
//
// Test also calls from/to pure functions.

type TupleIntInt = (i32, i32);
type TupleIntUsize = (i32, usize);
type TupleUsizeInt = (usize, i32);

trait Valid1 { #[pure] fn valid1(&self) -> bool; }
trait Valid2 { #[pure] fn valid2(&self) -> bool; }

#[refine_trait_spec] impl Valid1 for i32 {
    #[pure] fn valid1(&self) -> bool {
        *self == 3
    }
}
#[refine_trait_spec] impl Valid2 for i32 {
    #[pure] fn valid2(&self) -> bool {
        *self == 7
    }
}

#[refine_trait_spec] impl Valid1 for TupleIntInt {
    #[pure] fn valid1(&self) -> bool {
        let valid = (8, 9);
        *self == valid
    }
}
#[refine_trait_spec] impl Valid2 for TupleIntInt {
    #[pure] fn valid2(&self) -> bool {
        let valid = (4, 5);
        *self == valid
    }
}

#[refine_trait_spec] impl Valid1 for TupleIntUsize {
    #[pure] fn valid1(&self) -> bool {
        let valid = (42, 43);
        *self == valid
    }
}
#[refine_trait_spec] impl Valid1 for TupleUsizeInt {
    #[pure] fn valid1(&self) -> bool {
        let valid = (33, 44);
        *self == valid
    }
}

#[refine_trait_spec] impl Valid1 for bool {
    #[pure] fn valid1(&self) -> bool {
        *self
    }
}
#[refine_trait_spec] impl Valid2 for bool {
    #[pure] fn valid2(&self) -> bool {
        !*self
    }
}

#[trusted]
#[requires(a.valid1() && b.valid2())]
#[ensures(result.valid1())]
fn fn1<A: Valid1, B: Valid2, C: Valid1>(a: A, b: B) -> C { unimplemented!() }

#[trusted]
#[pure]
#[requires(a.valid1() && b.valid2())]
#[ensures(result.valid1())]
fn pure_fn1<A: Valid1 + Copy, B: Valid2 + Copy, C: Valid1 + Copy>(a: A, b: B) -> C { unimplemented!() }

#[requires(
    pure_fn1::<i32, (i32, i32), bool>(3, (4, 5))
)]
fn test_fn1() {
    assert!(fn1::<i32, (i32, i32), bool>(3, (4, 5)));
    assert!(pure_fn1::<i32, (i32, i32), bool>(3, (4, 5)));
}

#[trusted]
#[requires(a.valid2() && b.valid1())]
#[ensures(result.valid2())]
fn fn2<'a, 'b, A: Valid2, B: Valid1, C: Valid2>(a: &'a A, b: &'b B) -> C { unimplemented!() }

#[trusted]
#[pure]
#[requires(a.valid2() && b.valid1())]
#[ensures(result.valid2())]
fn pure_fn2<'a, 'b, A: Valid2, B: Valid1, C: Valid2 + Copy>(a: &'a A, b: &'b B) -> C { unimplemented!() }

// TODO: fold/unfold error when the precondition is enabled
/*
#[requires({
    let a = 7;
    let b = (8, 9);
    pure_fn2::<i32, (i32, i32), bool>(&a, &b);
})]
*/
fn test_fn2() {
    let a = 7;
    let b = (8, 9);
    assert!(!fn2::<i32, (i32, i32), bool>(&a, &b));
    assert!(!pure_fn2::<i32, (i32, i32), bool>(&a, &b));
}

struct X1<A, B>(A, B);
impl<A: Valid1, B: Valid2> X1<A, B> {
    #[trusted]
    #[requires(a.valid1() && b.valid2())]
    #[ensures(result.valid1())]
    fn fn3<'a, 'b, C: Valid1>(&self, a: &'a A, b: &'b B) -> C { unimplemented!() }

    #[trusted]
    #[pure]
    #[requires(a.valid1() && b.valid2())]
    #[ensures(result.valid1())]
    fn pure_fn3<'a, 'b, C: Valid1 + Copy>(&self, a: &'a A, b: &'b B) -> C { unimplemented!() }
}

fn test_fn3() {
    let a = 3;
    let b = (4, 5);
    let x = X1::<i32, (i32, i32)>(0, (0, 0));
    assert!(x.fn3::<bool>(&a, &b));
    assert!(x.pure_fn3::<bool>(&a, &b));
}

// Using `&'a A` or `&'b B` directly in `X2` fails because Prusti tries to
// encode the reference-typed fields `X2.0` resp. `X2.1`.
struct X2<'a, 'b, A, B>(std::marker::PhantomData<&'a A>, std::marker::PhantomData<&'b B>);
impl<'a, 'b, A: Valid2, B: Valid1> X2<'a, 'b, A, B> {
    #[trusted]
    #[requires(a.valid2() && b.valid1())]
    #[ensures(result.valid2())]
    fn fn4<C: Valid2>(&self, a: &'a A, b: &'b B) -> C { unimplemented!() }

    #[trusted]
    #[pure]
    #[requires(a.valid2() && b.valid1())]
    #[ensures(result.valid2())]
    fn pure_fn4<C: Valid2 + Copy>(&self, a: &'a A, b: &'b B) -> C { unimplemented!() }
}

fn test_fn4<'a, 'b>(x: X2<'a, 'b, i32, (i32, i32)>) {
    let a = 7;
    let b = (8, 9);
    assert!(!x.fn4::<bool>(&a, &b));
    assert!(!x.pure_fn4::<bool>(&a, &b));
}

trait T1 {
    #[requires(a.valid1() && b.valid2())]
    #[ensures(result.valid1())]
    fn fn5<A: Valid1, B: Valid2, C: Valid1>(&self, a: A, b: B) -> C;

    #[pure]
    #[requires(a.valid1() && b.valid2())]
    #[ensures(result.valid1())]
    fn pure_fn5<A: Valid1 + Copy, B: Valid2 + Copy, C: Valid1 + Copy>(&self, a: A, b: B) -> C;
}

struct X3 {}
impl T1 for X3 {
    #[trusted]
    fn fn5<A, B, C>(&self, a: A, b: B) -> C { unimplemented!() }

    #[trusted]
    #[pure]
    fn pure_fn5<A: Copy, B: Copy, C: Copy>(&self, a: A, b: B) -> C { unimplemented!() }
}

fn test_fn5<T: T1>(t: T, x: X3) {
    assert!(t.fn5::<i32, (i32, i32), bool>(3, (4, 5)));
    assert!(t.pure_fn5::<i32, (i32, i32), bool>(3, (4, 5)));
    assert!(x.fn5::<i32, (i32, i32), bool>(3, (4, 5)));
    assert!(x.pure_fn5::<i32, (i32, i32), bool>(3, (4, 5)));
}

trait T2 {
    type AT1: Valid1 + Copy;
    type AT2: Valid1 + Copy;

    // TODO: the c.valid1() && d.valid1() constraint causes a panic;
    //       we probably need to use the ParamEnv-respecting `local_mir`
    //       throughout the codebase

    #[requires(a.valid2() && b.valid1()
        // && c.valid1() && d.valid1()
    )]
    #[ensures(result.valid2())]
    fn fn6<A: Valid2, B: Valid1, C: Valid2>(&self, a: A, b: B, c: Self::AT1, d: Self::AT2) -> C;

    #[pure]
    #[requires(a.valid2() && b.valid1()
        // && c.valid1() && d.valid1()
    )]
    #[ensures(result.valid2())]
    fn pure_fn6<A: Valid2 + Copy, B: Valid1 + Copy, C: Valid2 + Copy>(&self, a: A, b: B, c: Self::AT1, d: Self::AT2) -> C;
}

struct X4 {}
impl T2 for X4 {
    type AT1 = (i32, usize);
    type AT2 = (usize, i32);

    #[trusted]
    fn fn6<A: Valid2, B: Valid1, C: Valid2>(&self, a: A, b: B, c: (i32, usize), d: (usize, i32)) -> C { unimplemented!() }

    #[trusted]
    #[pure]
    fn pure_fn6<A: Valid2 + Copy, B: Valid1 + Copy, C: Valid2 + Copy>(&self, a: A, b: B, c: (i32, usize), d: (usize, i32)) -> C { unimplemented!() }
}

fn test_fn6<T: T2<AT1 = (i32, usize), AT2 = (usize, i32)>>(t: T, x: X4) {
    assert!(!t.fn6::<i32, (i32, i32), bool>(7, (8, 9), (42, 43), (33, 44)));
    assert!(!t.pure_fn6::<i32, (i32, i32), bool>(7, (8, 9), (42, 43), (33, 44)));
    assert!(!x.fn6::<i32, (i32, i32), bool>(7, (8, 9), (42, 43), (33, 44)));
    assert!(!x.pure_fn6::<i32, (i32, i32), bool>(7, (8, 9), (42, 43), (33, 44)));
}

#[trusted]
fn main() {}
