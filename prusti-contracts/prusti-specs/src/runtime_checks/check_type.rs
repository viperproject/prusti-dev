#[derive(Clone, Copy, PartialEq)]
pub enum CheckItemType {
    PledgeLhs,
    PledgeRhs { has_lhs: bool },
    Requires,
    Ensures,
    Assert,
    Assume,
    BodyInvariant,
    Unchecked,
}

impl CheckItemType {
    pub(crate) fn gets_old_args(&self) -> bool {
        matches!(
            self,
            Self::PledgeLhs | Self::PledgeRhs { .. } | Self::Ensures
        )
    }

    // probably pledge_rhs shouldn't actually need it..
    pub(crate) fn needs_result(&self) -> bool {
        matches!(
            self,
            Self::PledgeLhs | Self::PledgeRhs { .. } | Self::Ensures
        )
    }

    pub(crate) fn gets_item_args(&self) -> bool {
        // maybe pledge_rhs should not get items either
        matches!(
            self,
            Self::PledgeRhs { .. } | Self::Requires | Self::Ensures
        )
    }

    pub(crate) fn is_inlined(&self) -> bool {
        matches!(self, Self::Assert | Self::Assume | Self::BodyInvariant)
    }

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
            Self::Unchecked => unreachable!(),
        }
    }
}

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
            Self::Unchecked => unreachable!(),
        }
    }
}
