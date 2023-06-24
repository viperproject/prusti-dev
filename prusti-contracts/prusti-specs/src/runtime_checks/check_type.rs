use crate::rewriter::SpecItemType;

#[derive(Clone, Copy, Debug)]
pub enum CheckType {
    Postcondition,
    Precondition,
    Pledge,
    // Closure expressions contain loop_invariant, prusti_assume and prusti_assert
    // there is no need to distinguis them further
    ClosureExpression,
}

impl CheckType {
    // whether or not we can generate a function on the ast level that
    // generates an old_values tuple for arguments used in old expressions.
    // This is ufnortunately not possible for ClosureExpressions, therefore they
    // will have to be encoded differently
    pub fn has_old_tuple(&self) -> bool {
        matches!(self, Self::Postcondition | Self::Pledge)
    }

    pub fn is_closure(&self) -> bool {
        matches!(self, Self::ClosureExpression)
    }

    pub fn from_spectype(spec: &SpecItemType) -> Self {
        match spec {
            SpecItemType::Postcondition => Self::Postcondition,
            SpecItemType::Precondition => Self::Precondition,
            SpecItemType::Pledge => Self::Pledge,
            _ => panic!("spec type {:?} are not supported to be translated to runtime-checks.", spec)
        }
    }
}
