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
    /// Check only the core proof of the procedure.
    CoreProof,
    /// Check only the specifications of the procedure.
    Specifications,
    /// Check both the specification and the core proof.
    Both,
}
