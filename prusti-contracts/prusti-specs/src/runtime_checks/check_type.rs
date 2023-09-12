#[derive(Clone, Copy, PartialEq)]
pub(crate) enum CheckItemType {
    PledgeLhs,
    PledgeRhs { has_lhs: bool },
    Requires,
    Ensures,
    Assert,
    Assume,
    BodyInvariant,
    Predicate,
    Unchecked,
}

impl CheckItemType {
    /// Whether the signature of the check function generated from this contract
    /// will contain old_values
    pub(crate) fn gets_old_args(&self) -> bool {
        matches!(
            self,
            Self::PledgeLhs | Self::PledgeRhs { .. } | Self::Ensures
        )
    }

    /// Whether the result of the function needs to be part of the check functions signature.
    pub(crate) fn needs_result(&self) -> bool {
        matches!(
            self,
            Self::PledgeLhs | Self::PledgeRhs { .. } | Self::Ensures
        )
    }

    /// Whether the original arguments to the function are also passed to
    /// the check function. Maybe pledges shouldn't be here.
    pub(crate) fn gets_item_args(&self) -> bool {
        // maybe pledge_rhs should not get items either
        matches!(
            self,
            Self::PledgeRhs { .. } | Self::Requires | Self::Ensures | Self::Predicate
        )
    }

    /// Whether this kind of contract only occurrs within code, not as an annotation
    /// of functions
    pub(crate) fn is_inlined(&self) -> bool {
        matches!(self, Self::Assert | Self::Assume | Self::BodyInvariant)
    }

    /// A helper function for pretty printing contracts, allowing us a prettier
    /// output for runtime errors
    pub(crate) fn wrap_contract(&self, s: &String) -> String {
        match self {
            Self::PledgeLhs => format!("#[assert_on_expiry({}, ..)]", s),
            Self::PledgeRhs { has_lhs } => {
                if *has_lhs {
                    format!("#[assert_on_expiry(.., {})]", s)
                } else {
                    format!("#[after_expiry({})]", s)
                }
            }
            Self::Requires => format!("#[requires({})]", s),
            Self::Ensures => format!("#[ensures({})]", s),
            Self::Assert => format!("prusti_assert!({})", s),
            Self::Assume => format!("prusti_assume!({})", s),
            Self::BodyInvariant => format!("body_invariant!({})", s),
            Self::Predicate => format!("predicate!{{ {} }}", s),
            Self::Unchecked => unreachable!(),
        }
    }

    pub(crate) fn can_be_checked(&self) -> bool {
        !matches!(self, Self::Unchecked)
    }
}

/// Opposed to previous debugging output, this one is used for generating the
/// check function names.
impl std::fmt::Display for CheckItemType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PledgeLhs => write!(f, "pledge_lhs"),
            Self::PledgeRhs { .. } => write!(f, "pledge"),
            Self::Requires => write!(f, "pre"),
            Self::Ensures => write!(f, "post"),
            Self::Assert => write!(f, "assert"),
            Self::Assume => write!(f, "assume"),
            Self::BodyInvariant => write!(f, "body_invariant"),
            Self::Predicate => write!(f, "predicate"),
            Self::Unchecked => unreachable!(),
        }
    }
}
