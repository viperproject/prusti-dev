use serde::Serialize;
use viper::VerificationResult;

// since the existing verification result
// is not as trivially passed in json
#[derive(Serialize)]
pub struct IdeVerificationResult {
    item_name: String,
    success: bool,
    time_ms: u128,
    cached: bool,
}

impl IdeVerificationResult {
    pub fn from_res(res: &VerificationResult) -> Self {
        Self {
            item_name: res.item_name.clone(),
            success: res.is_success(),
            time_ms: res.time_ms,
            cached: res.cached,
        }
    }
}
