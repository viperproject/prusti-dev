#[derive(
    Clone,
    Copy,
    Debug,
    derive_more::Display,
    PartialEq,
    Eq,
    serde::Serialize,
    serde::Deserialize,
    Hash,
)]
pub enum CheckMode {
    /// Check only that the safe procedure is memory safe.
    MemorySafety,
    /// Check that the safe procedure is memory safe and that it satisfies its
    /// function contract.
    MemorySafetyWithFunctional,
    /// Check that the safe procedure is memory safe and that it can be soundly
    /// purified.
    PurificationSoudness,
    /// Check that the safe purified procedure statisfies its function contract.
    PurificationFunctional,
    /// Check that the unsafe procedure is memory safe and that it satisfies its
    /// function contract.
    UnsafeSafety,
}

impl CheckMode {
    pub fn check_core_proof(&self) -> bool {
        matches!(
            self,
            Self::MemorySafety
                | Self::MemorySafetyWithFunctional
                | Self::PurificationSoudness
                | Self::UnsafeSafety
        )
    }

    pub fn check_specifications(&self) -> bool {
        matches!(
            self,
            Self::MemorySafetyWithFunctional | Self::PurificationFunctional | Self::UnsafeSafety
        )
    }

    pub fn is_purification_group(&self) -> bool {
        matches!(
            self,
            Self::PurificationSoudness | Self::PurificationFunctional
        )
    }

    pub fn supports_accessibility_predicates_in_assertions(&self) -> bool {
        matches!(
            self,
            Self::MemorySafety | Self::MemorySafetyWithFunctional | Self::UnsafeSafety
        )
    }
}
