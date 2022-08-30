use std::{convert::TryFrom, cmp::Ordering};

/// This type identifies one of the procedural macro attributes of Prusti
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum SpecAttributeKind {
    Requires,
    Ensures,
    AfterExpiry,
    AssertOnExpiry,
    Pure,
    Trusted,
    Predicate,
    Invariant,
    GhostConstraint,
    Model, 
    PrintCounterexample,
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

impl Ord for SpecAttributeKind {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other){
            (SpecAttributeKind::Model, _) => Ordering::Less,
            (_, SpecAttributeKind::Model) => Ordering::Greater,
            _ => Ordering::Equal,
        }
    }
}

impl PartialOrd for SpecAttributeKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}