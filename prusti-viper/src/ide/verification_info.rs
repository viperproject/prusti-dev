use viper::VerificationResult;
use serde::Serialize;

#[derive(Serialize)]
pub struct VerificationInfo {
    result_list: Vec<IdeVerificationResult>
}

impl VerificationInfo {
    pub fn new() -> Self {
        Self {
            result_list: vec![],
        }
    }
    pub fn add(&mut self, res: &VerificationResult) {
        let ide_res = IdeVerificationResult::from_res(res);
        self.result_list.push(ide_res);
    }
    pub fn to_json_string(self) -> String {
        serde_json::to_string(&self).unwrap()
    }
}

// since the existing verification result
// is not as trivially passed in json
#[derive(Serialize)]
pub struct IdeVerificationResult {
    item_name: String,
    success: bool,
    time_ms: u128,
    cached: bool
}

impl IdeVerificationResult {
    pub fn from_res(res: &VerificationResult) -> Self {
        match res {
            _ => {
                Self {
                    item_name: res.item_name.clone(),
                    success: res.is_success(),
                    time_ms: res.time_ms,
                    cached: res.cached,
                }
            }
        }
    }
}
