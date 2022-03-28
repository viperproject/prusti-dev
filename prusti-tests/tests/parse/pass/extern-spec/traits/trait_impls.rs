use prusti_contracts::*;

/// External types
trait ExternTrait {
    type Arg1Ty;
    type Arg2Ty;
    type Ret1Ty;
    type Ret2Ty;

    fn foo(&self, x: Self::Arg1Ty, y: Self::Arg2Ty) -> Self::Ret1Ty;
    fn bar(&self) -> Self::Ret2Ty;
}
struct Dummy;
impl ExternTrait for Dummy {
    type Arg1Ty = i32;
    type Arg2Ty = i32;
    type Ret1Ty = i32;
    type Ret2Ty = i32;

    fn foo(&self, x: Self::Arg1Ty, y: Self::Arg2Ty) -> Self::Ret1Ty { 0 }
    fn bar(&self) -> Self::Ret2Ty { 0 }
}
/// External types

#[extern_spec]
impl ExternTrait for Dummy {
    #[requires(x > 0)]
    fn foo(&self, x: Self::Arg1Ty, y: Self::Arg2Ty) -> Self::Ret1Ty;
}

fn main() {}
