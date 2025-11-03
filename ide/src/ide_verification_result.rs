use serde::Serialize;

/// Generated for each verification item, containing information
/// about the result of the verification. This information will be emitted
/// if the show_ide_info flag is set, and it's purpose is to be
/// consumed by prusti-assistant.
#[derive(Serialize)]
pub struct IdeVerificationResult {
    /// the name / defpath of the method
    pub item_name: String,
    /// whether the verification of that method was successful
    pub success: bool,
    /// how long the verification took
    pub time_ms: u128,
    /// whether this result was cached or is fresh
    pub cached: bool,
}
