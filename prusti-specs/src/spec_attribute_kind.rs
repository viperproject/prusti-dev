use std::convert::TryFrom;

/// This type identifies one of the procedural macro attributes of Prusti
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum SpecAttributeKind {
    Requires,
    Ensures,
    AfterExpiry,
    Pure,
    Trusted,
    Predicate,
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "after_expiry" => Ok(SpecAttributeKind::AfterExpiry),
            "pure" => Ok(SpecAttributeKind::Pure),
            "trusted" => Ok(SpecAttributeKind::Trusted),
            "predicate" => Ok(SpecAttributeKind::Predicate),
            _ => Err(name),
        }
    }
}
