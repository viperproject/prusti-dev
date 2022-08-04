// compile-flags: -Penable_ghost_constraints=true

#![feature(unboxed_closures, fn_traits)]

use prusti_contracts::*;

pub trait ClosureSpecExt<A> : FnMut<A> {
    predicate! { fn call_pre(&self, args: &A) -> bool; }
    predicate! { fn call_post(prev: &Self, curr: &Self, args: &A, res: &Self::Output) -> bool; }
    predicate! { fn hist_inv(prev: &Self, curr: &Self) -> bool; }
}

#[extern_spec]
trait FnMut<#[generic] A> {
    #[ghost_constraint(Self: ClosureSpecExt<A> , [
        requires(<Self as ClosureSpecExt<A>>::hist_inv(&self, &self)),
        requires(<Self as ClosureSpecExt<A>>::call_pre(&self, &args)),
        ensures(<Self as ClosureSpecExt<A>>::hist_inv(old(&self), &self)),
        ensures(<Self as ClosureSpecExt<A>>::call_post(old(&self), &self, &args, &result)),
    ])]
    fn call_mut(&mut self, args: A) -> <Self as FnOnce<A>>::Output;
}

// encoding of:
// #[requires(x >= 5)]
// #[ensures(result == x + val)]
// #[ensures(val == old(val) + 1)]
// #[invariant(val >= old(val))]
// |x: i32| { val += 1; x + val }

struct MyClosure {
    val: i32,
}

impl FnOnce<(i32,)> for MyClosure {
    type Output = i32;
    extern "rust-call" fn call_once(mut self, args: (i32,)) -> i32 {
        self.val += 1;
        args.0 + self.val
    }
}
impl FnMut<(i32,)> for MyClosure {
    extern "rust-call" fn call_mut(&mut self, args: (i32,)) -> i32 {
        self.val += 1;
        args.0 + self.val
    }
}
#[refine_trait_spec]
impl ClosureSpecExt<(i32,)> for MyClosure {
    predicate! { fn call_pre(&self, args: &(i32,)) -> bool {
        args.0 >= 5
    } }
    predicate! { fn call_post(prev: &Self, curr: &Self, args: &(i32,), res: &i32) -> bool {
        *res == args.0 + curr.val
        && curr.val == prev.val + 1
    } }
    predicate! { fn hist_inv(prev: &Self, curr: &Self) -> bool {
        curr.val >= prev.val
    } }
}

fn main() {
    let mut cl = MyClosure { val: 3 };
    cl(3); //~ ERROR precondition might not hold
}
