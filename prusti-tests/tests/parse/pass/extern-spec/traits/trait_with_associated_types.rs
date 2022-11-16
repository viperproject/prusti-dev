use prusti_contracts::*;

/// External traits
trait ExternTrait {
    type Arg1Ty;
    type Arg2Ty;
    type Ret1Ty;
    type Ret2Ty;

    fn foo(&self, x: Self::Arg1Ty, y: Self::Arg2Ty) -> Self::Ret1Ty;
    fn bar(&self) -> Self::Ret2Ty;
}
/// External traits

#[extern_spec]
trait ExternTrait {
    fn foo(&self, x: Self::Arg1Ty, y: Self::Arg2Ty) -> Self::Ret1Ty;
}

fn main() {}
