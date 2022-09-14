use std::convert::TryFrom;

/// This type identifies one of the procedural macro attributes of Prusti
#[derive(PartialEq, Eq, Copy, Clone, Debug, PartialOrd, Ord)]
pub enum SpecAttributeKind {
    /// All type specifications that alter its type must be processed before 
    /// PrintCounterexample. Currently this only applies to Model. 
    Model = 0,
    Requires = 1,
    Ensures = 2,
    AfterExpiry = 3,
    AssertOnExpiry = 4,
    Pure = 5,
    Trusted = 6,
    Predicate = 7,
    Invariant = 8,
    GhostConstraint = 9,
    PrintCounterexample = 10,
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "after_expiry" => Ok(SpecAttributeKind::AfterExpiry),
            "assert_on_expiry" => Ok(SpecAttributeKind::AssertOnExpiry),
            "pure" => Ok(SpecAttributeKind::Pure),
            "trusted" => Ok(SpecAttributeKind::Trusted),
            "predicate" => Ok(SpecAttributeKind::Predicate),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            "ghost_constraint" => Ok(SpecAttributeKind::GhostConstraint),
            "model" => Ok(SpecAttributeKind::Model),
            "print_counterexample" => Ok(SpecAttributeKind::PrintCounterexample),
            _ => Err(name),
        }
    }
}
