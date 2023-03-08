use serde::Serialize;
use viper::VerificationResult;

/// Generated for each verification item, containing information
/// about the result of the verification. This information will be emitted
/// if the show_ide_info flag is set, and it's purpose is to be
/// consumed by prusti-assistant.
#[derive(Serialize)]
pub struct IdeVerificationResult {
    /// the name / defpath of the method
    item_name: String,
    /// whether the verification of that method was successful
    success: bool,
    /// how long the verification took
    time_ms: u128,
    /// whether this result was cached or is fresh
    cached: bool,
}

impl From<&VerificationResult> for IdeVerificationResult {
    fn from(res: &VerificationResult) -> Self {
        Self {
            item_name: res.item_name.clone(),
            success: res.is_success(),
            time_ms: res.time_ms,
            cached: res.cached,
        }
    }
}
